package com.kurdo.litevpn

import android.content.Context
import android.util.Base64
import com.jcraft.jsch.ChannelDirectTCPIP
import com.jcraft.jsch.JSch
import com.jcraft.jsch.Session
import com.jcraft.jsch.SocketFactory
import org.json.JSONArray
import org.json.JSONObject
import java.io.BufferedReader
import java.io.ByteArrayOutputStream
import java.io.DataInputStream
import java.io.File
import java.io.InputStream
import java.io.InputStreamReader
import java.io.OutputStream
import java.io.PushbackInputStream
import java.net.DatagramPacket
import java.net.DatagramSocket
import java.net.InetAddress
import java.net.InetSocketAddress
import java.net.ServerSocket
import java.net.Socket
import java.net.URI
import java.nio.ByteBuffer
import java.security.MessageDigest
import java.security.SecureRandom
import java.security.cert.X509Certificate
import java.util.Properties
import java.util.UUID
import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.CopyOnWriteArrayList
import java.util.concurrent.Executors
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicInteger
import javax.net.ssl.SNIHostName
import javax.net.ssl.SSLContext
import javax.net.ssl.SSLParameters
import javax.net.ssl.SSLSocket
import javax.net.ssl.TrustManager
import javax.net.ssl.X509TrustManager

object TunnelEngine {

    private val running = AtomicBoolean(false)
    private var sshSession: Session? = null
    private val sshSessionPool = CopyOnWriteArrayList<Session>()
    private val sshRoundRobin = AtomicInteger(0)
    private var socksServer: ServerSocket? = null
    private var httpServer: ServerSocket? = null
    private var httpAltServer: ServerSocket? = null
    private var udpgwLocalServer: ServerSocket? = null
    private var dnsGatewaySocket: DatagramSocket? = null
    private var dnsttProcess: Process? = null
    private var dnsttBalancerServer: ServerSocket? = null
    private val dnsttProcesses = CopyOnWriteArrayList<Process>()
    private val dnsttSessionPorts = CopyOnWriteArrayList<Int>()
    private val dnsttRoundRobin = AtomicInteger(0)
    private var v2rayProcess: Process? = null
    private var isNativeV2RayActive = AtomicBoolean(false)
    private var activeConfig: JSONObject = JSONObject()
    private var appContext: Context? = null
    private val pool = Executors.newCachedThreadPool()
    private val rng = SecureRandom()

    const val LOCAL_DNS_GW_PORT = 8091
    const val LOCAL_DNSTT_PORT = 7000

    private class CachedDnsEntry(val response: ByteArray, val expiryMs: Long)
    private val dnsCache = ConcurrentHashMap<String, CachedDnsEntry>()

    fun start(
        context: Context,
        configJson: String,
        onState: (String, String) -> Unit,
        onLog: (String) -> Unit
    ) {
        stop()
        appContext = context.applicationContext
        running.set(true)
        activeConfig = JSONObject(configJson)
        pool.execute {
            runSupervisor(activeConfig, onState, onLog)
        }
    }

    fun stop() {
        running.set(false)
        dnsCache.clear()
        isNativeV2RayActive.set(false)
        try { socksServer?.close() } catch (ignored: Exception) {}
        try { httpServer?.close() } catch (ignored: Exception) {}
        try { httpAltServer?.close() } catch (ignored: Exception) {}
        try { udpgwLocalServer?.close() } catch (ignored: Exception) {}
        try { dnsGatewaySocket?.close() } catch (ignored: Exception) {}
        try { v2rayProcess?.destroy() } catch (ignored: Exception) {}
        try { dnsttBalancerServer?.close() } catch (ignored: Exception) {}
        dnsttBalancerServer = null
        try { dnsttProcess?.destroy() } catch (ignored: Exception) {}
        for (p in dnsttProcesses) {
            try { p.destroy() } catch (ignored: Exception) {}
        }
        dnsttProcesses.clear()
        dnsttSessionPorts.clear()
        for (s in sshSessionPool) {
            try { s.disconnect() } catch (ignored: Exception) {}
        }
        sshSessionPool.clear()
        try { sshSession?.disconnect() } catch (ignored: Exception) {}
        socksServer = null
        httpServer = null
        httpAltServer = null
        udpgwLocalServer = null
        dnsGatewaySocket = null
        v2rayProcess = null
        dnsttProcess = null
        sshSession = null
    }

    fun onNetworkHandover(onLog: (String) -> Unit) {
        if (!running.get()) return
        onLog("Network switch detected -> verifying active tunnel...")
        pool.execute {
            try {
                sshSession?.sendKeepAliveMsg()
                for (s in sshSessionPool) {
                    if (s.isConnected) s.sendKeepAliveMsg()
                }
            } catch (ignored: Exception) {
                onLog("Rebinding tunnel after network handover...")
                for (s in sshSessionPool) {
                    try { s.disconnect() } catch (ignored: Exception) {}
                }
                try { sshSession?.disconnect() } catch (ignored: Exception) {}
            }
        }
    }

    private fun runSupervisor(
        cfg: JSONObject,
        onState: (String, String) -> Unit,
        onLog: (String) -> Unit
    ) {
        val useV2ray = cfg.optBoolean("use_v2ray", false)
        val useSlowDns = cfg.optBoolean("use_slowdns", false)
        val enableShareNet = cfg.optBoolean("enable_sharenet", false)
        val socksPort = cfg.optInt("sharenet_socks_port", 10808)
        val httpPort = cfg.optInt("sharenet_http_port", 8080)
        val bindAddr = if (enableShareNet) "0.0.0.0" else "127.0.0.1"

        // Always start the Local UDP DNS Gateway on 127.0.0.1:8091 for libtun2socks.so
        startLocalDnsGateway(cfg, onLog)

        if (useSlowDns) {
            startNativeSlowDnsProcess(cfg, onLog)
        }

        // Check if native libv2ray.so (Xray-core) binary is available when V2Ray mode is selected
        val ctx = appContext
        val libV2rayFile = if (ctx != null) File(ctx.applicationInfo.nativeLibraryDir, "libv2ray.so") else null
        var canUseNativeXray = useV2ray && libV2rayFile != null && libV2rayFile.exists()

        fun ensureLocalSocksListeners(): Boolean {
            if (socksServer != null && socksServer?.isClosed == false) return true
            return try {
                socksServer = ServerSocket()
                socksServer?.reuseAddress = true
                socksServer?.bind(InetSocketAddress("0.0.0.0", socksPort))
                pool.execute { acceptSocks5Loop(socksServer!!, onLog) }
                true
            } catch (e: Exception) {
                onState("ERROR", "Local proxy bind failed: ${e.message}")
                false
            }
        }

        // Always start Kotlin HTTP/SOCKS5 ShareNet proxy listeners when ShareNet is enabled
        // (works across SSH, SlowDNS, Native Xray, and Built-in V2Ray!)
        if (enableShareNet) {
            startShareNetProxyServers(httpPort, socksPort, onLog)
        }

        if (!canUseNativeXray) {
            if (!ensureLocalSocksListeners()) return
        }

        var backoffMs = 2000L
        while (running.get()) {
            try {
                onState("CONNECTING", "Starting tunnel...")
                if (canUseNativeXray) {
                    val fallbackNeeded = !runNativeXrayCore(libV2rayFile!!, cfg, onState, onLog)
                    if (fallbackNeeded && running.get()) {
                        onLog("Switching to built-in V2Ray engine for compatibility...")
                        canUseNativeXray = false
                        if (!ensureLocalSocksListeners()) return
                        connectOnce(cfg, onState, onLog)
                    }
                } else {
                    connectOnce(cfg, onState, onLog)
                }
                backoffMs = 2000L
            } catch (e: Exception) {
                if (!running.get()) break
                onLog("Tunnel error: ${e.message} (retry in ${backoffMs / 1000}s)")
                onState("RECONNECTING", e.message ?: "Retrying")
                try { Thread.sleep(backoffMs) } catch (ignored: Exception) {}
                if (backoffMs < 20000L) backoffMs *= 2
            }
        }
        onState("DISCONNECTED", "Stopped")
    }

    /**
     * Launches the native Xray-core binary (libv2ray.so) with automatic retry if Xray v26+
     * rejects allowInsecure:true, and returns false if built-in V2Ray engine fallback is needed.
     */
    private fun runNativeXrayCore(
        libV2rayFile: File,
        cfg: JSONObject,
        onState: (String, String) -> Unit,
        onLog: (String) -> Unit
    ): Boolean {
        val ctx = appContext ?: return false
        try { libV2rayFile.setExecutable(true) } catch (ignored: Throwable) {}

        val useSlowDns = cfg.optBoolean("use_slowdns", false)
        val slowDnsSessions = cfg.optInt("dnstt_sessions", 4).coerceIn(1, 8)
        val proto = cfg.optString("v2ray_proto", "vless").uppercase()
        val net = cfg.optString("v2ray_net", "ws").uppercase()
        val sec = cfg.optString("v2ray_security", if (cfg.optBoolean("v2ray_tls", true)) "tls" else "none").uppercase()
        val modeLabel = if (useSlowDns) "Xray ($proto/$net/$sec) over SlowDNS (${slowDnsSessions}x)" else "Xray ($proto/$net/$sec)"

        // Try first with allowInsecure=true (for self-signed VPS certs / SNI bug hosts on Xray <= v25),
        // and if Xray v26+ rejects allowInsecure, immediately retry with allowInsecure omitted.
        for (includeAllowInsecure in listOf(true, false)) {
            if (!running.get()) return true
            try { v2rayProcess?.destroy() } catch (ignored: Exception) {}

            val xrayConfigJson = buildXrayConfigJson(cfg, onLog, includeAllowInsecure)
            val cfgFile = File(ctx.filesDir, "v2ray_config.json")
            cfgFile.writeText(xrayConfigJson.toString(2))

            if (includeAllowInsecure) {
                onLog("Launching Native libv2ray.so -> $modeLabel")
            } else {
                onLog("Retrying libv2ray.so with Xray v26 strict TLS config...")
            }

            val proc = try {
                val pb = ProcessBuilder(libV2rayFile.absolutePath, "run", "-c", cfgFile.absolutePath)
                pb.directory(ctx.filesDir)
                pb.redirectErrorStream(true)
                pb.start()
            } catch (e: Exception) {
                onLog("Native libv2ray.so exec note: ${e.message}")
                return false
            }

            v2rayProcess = proc
            isNativeV2RayActive.set(true)

            val recentLines = CopyOnWriteArrayList<String>()
            pool.execute {
                try {
                    val reader = BufferedReader(InputStreamReader(proc.inputStream))
                    var line: String?
                    while (reader.readLine().also { line = it } != null) {
                        val l = line?.trim() ?: continue
                        if (l.isNotEmpty()) {
                            recentLines.add(l)
                            onLog("Xray: $l")
                        }
                    }
                } catch (ignored: Exception) {}
            }

            Thread.sleep(750)
            if (proc.isAlive) {
                onLog("Connected! Native $modeLabel active -> starting TUN2SOCKS.")
                onState("CONNECTED", modeLabel)

                while (running.get() && proc.isAlive) {
                    Thread.sleep(2000L)
                }
                isNativeV2RayActive.set(false)
                if (running.get()) {
                    throw Exception("Xray process terminated unexpectedly")
                }
                return true
            }

            isNativeV2RayActive.set(false)
            val combinedOut = recentLines.joinToString(" | ")
            if (includeAllowInsecure && combinedOut.contains("allowInsecure", ignoreCase = true)) {
                continue
            } else {
                break
            }
        }

        return false
    }

    /**
     * Builds a complete Xray-core JSON configuration supporting:
     * - VLESS / VMess / Trojan (strictly 1 server in vnext/servers for Xray v25/v26 compatibility)
     * - TLS / XTLS-Reality (pbk, sid, spx, uTLS fingerprint) / XTLS Vision flow
     * - TCP / WebSocket / gRPC / HTTPUpgrade
     * - V2Ray over SlowDNS (dials local 127.0.0.1:7000 SlowDNS load-balancer while keeping SNI & Host headers)
     */
    private fun buildXrayConfigJson(
        cfg: JSONObject,
        onLog: (String) -> Unit,
        includeAllowInsecure: Boolean = true
    ): JSONObject {
        val rawCustomJson = cfg.optString("v2ray_raw_json", "").trim()
        if (rawCustomJson.startsWith("{") && rawCustomJson.endsWith("}")) {
            try {
                onLog("Using custom raw Xray JSON configuration")
                return JSONObject(rawCustomJson)
            } catch (ignored: Exception) {}
        }

        val socksPort = cfg.optInt("sharenet_socks_port", 10808)
        val httpPort = cfg.optInt("sharenet_http_port", 8080)
        val enableShareNet = cfg.optBoolean("enable_sharenet", false)
        val listenIp = if (enableShareNet) "0.0.0.0" else "127.0.0.1"

        val useSlowDns = cfg.optBoolean("use_slowdns", false)
        val proto = cfg.optString("v2ray_proto", "vless").lowercase()
        val remoteHost = cfg.optString("v2ray_host", "").ifEmpty { cfg.optString("server_host", "127.0.0.1") }.ifEmpty { "127.0.0.1" }
        val remotePort = cfg.optInt("v2ray_port", 443).let { if (it in 1..65535) it else 443 }

        val slowDnsSessions = if (useSlowDns) cfg.optInt("dnstt_sessions", 4).coerceIn(1, 8) else 1
        val dialAddress = if (useSlowDns) "127.0.0.1" else remoteHost
        val sessionPorts = if (useSlowDns) {
            if (dnsttSessionPorts.isNotEmpty()) dnsttSessionPorts.toList()
            else (0 until slowDnsSessions).map { LOCAL_DNSTT_PORT + it }
        } else {
            listOf(remotePort)
        }

        val rawUuid = cfg.optString("v2ray_uuid", "").trim().ifEmpty { cfg.optString("ssh_pass", "").trim() }
        if (rawUuid.isEmpty()) {
            onLog("V2Ray notice: UUID/Password is empty in V2Ray Config!")
        }
        val validUuid = try {
            UUID.fromString(rawUuid).toString()
        } catch (ignored: Exception) {
            UUID.nameUUIDFromBytes((rawUuid.ifEmpty { "kurdolite-default-uuid" }).toByteArray(Charsets.UTF_8)).toString()
        }

        val flow = cfg.optString("v2ray_flow", "").trim()
        val net = cfg.optString("v2ray_net", "ws").lowercase()
        val path = cfg.optString("v2ray_path", "/").ifEmpty { "/" }
        val sni = cfg.optString("v2ray_sni", "").ifEmpty { cfg.optString("sni", remoteHost) }.ifEmpty { remoteHost }
        val security = cfg.optString("v2ray_security", if (cfg.optBoolean("v2ray_tls", true)) "tls" else "none").lowercase()
        val fp = cfg.optString("v2ray_fp", "chrome").ifEmpty { "chrome" }
        val pbk = cfg.optString("v2ray_pbk", "").trim()
        val sid = cfg.optString("v2ray_sid", "").trim()
        val spx = cfg.optString("v2ray_spx", "/").ifEmpty { "/" }

        val inbounds = JSONArray().apply {
            put(JSONObject().apply {
                put("tag", "socks-in")
                put("port", socksPort)
                put("listen", "0.0.0.0")
                put("protocol", "socks")
                put("sniffing", JSONObject().apply {
                    put("enabled", true)
                    put("destOverride", JSONArray().put("http").put("tls"))
                    put("routeOnly", true)
                })
                put("settings", JSONObject().apply {
                    put("auth", "noauth")
                    put("udp", true)
                })
            })
        }

        fun makeOutboundSettingsForPort(targetPort: Int): JSONObject {
            return when (proto) {
                "trojan" -> JSONObject().apply {
                    put("servers", JSONArray().put(JSONObject().apply {
                        put("address", dialAddress)
                        put("port", targetPort)
                        put("password", rawUuid.ifEmpty { "password" })
                    }))
                }
                "vmess" -> JSONObject().apply {
                    put("vnext", JSONArray().put(JSONObject().apply {
                        put("address", dialAddress)
                        put("port", targetPort)
                        put("users", JSONArray().put(JSONObject().apply {
                            put("id", validUuid)
                            put("security", "auto")
                        }))
                    }))
                }
                else -> JSONObject().apply {
                    put("vnext", JSONArray().put(JSONObject().apply {
                        put("address", dialAddress)
                        put("port", targetPort)
                        put("users", JSONArray().put(JSONObject().apply {
                            put("id", validUuid)
                            put("encryption", "none")
                            if (flow.isNotEmpty() && (net == "tcp" || net == "raw")) {
                                put("flow", flow)
                            }
                        }))
                    }))
                }
            }
        }

        val streamSettings = JSONObject().apply {
            put("network", net)
            put("security", security)

            when (security) {
                "reality" -> {
                    put("realitySettings", JSONObject().apply {
                        put("show", false)
                        put("fingerprint", fp)
                        put("serverName", sni)
                        put("publicKey", pbk)
                        put("shortId", sid)
                        put("spiderX", spx)
                    })
                }
                "tls" -> {
                    put("tlsSettings", JSONObject().apply {
                        if (includeAllowInsecure) {
                            put("allowInsecure", true)
                        }
                        put("serverName", sni)
                        put("fingerprint", fp)
                    })
                }
            }

            when (net) {
                "ws" -> {
                    put("wsSettings", JSONObject().apply {
                        put("path", path)
                        put("host", sni)
                        put("headers", JSONObject().apply {
                            put("Host", sni)
                        })
                    })
                }
                "grpc" -> {
                    put("grpcSettings", JSONObject().apply {
                        put("serviceName", path.removePrefix("/"))
                        put("multiMode", true)
                    })
                }
                "httpupgrade" -> {
                    put("httpupgradeSettings", JSONObject().apply {
                        put("path", path)
                        put("host", sni)
                    })
                }
            }
        }

        // Enable mux when running over SlowDNS (without XTLS flow) so Xray reuses established TLS tunnels
        // instead of performing a new TLS handshake over DNS for every app socket!
        val useMux = useSlowDns && flow.isEmpty()
        val muxObj = JSONObject().apply {
            put("enabled", useMux)
            if (useMux) {
                put("concurrency", 8)
                put("xudpConcurrency", 8)
                put("xudpProxyUDP443", "reject")
            }
        }

        val outbounds = JSONArray().apply {
            val validProto = if (proto in listOf("vless", "vmess", "trojan")) proto else "vless"
            for ((idx, p) in sessionPorts.withIndex()) {
                val tag = if (sessionPorts.size == 1) "V2RAY" else "V2RAY_${idx + 1}"
                put(JSONObject().apply {
                    put("tag", tag)
                    put("protocol", validProto)
                    put("settings", makeOutboundSettingsForPort(p))
                    put("streamSettings", streamSettings)
                    put("mux", muxObj)
                })
            }
            put(JSONObject().apply {
                put("tag", "block-quic")
                put("protocol", "blackhole")
            })
            put(JSONObject().apply {
                put("tag", "direct")
                put("protocol", "freedom")
            })
        }

        val routing = JSONObject().apply {
            put("domainStrategy", "AsIs")
            val rules = JSONArray().apply {
                // Route libtun2socks.so BadVPN UDPGW connections (127.0.0.1:7300) to our local UDPGW/DNS engine!
                put(JSONObject().apply {
                    put("type", "field")
                    put("ip", JSONArray().put("127.0.0.1"))
                    put("port", "7300")
                    put("outboundTag", "direct")
                })
                // Reject QUIC (UDP 443) immediately so YouTube, Instagram, Facebook, TikTok & Chrome
                // switch to TCP 443 in <1ms instead of hanging on UDP 443!
                put(JSONObject().apply {
                    put("type", "field")
                    put("network", "udp")
                    put("port", "443")
                    put("outboundTag", "block-quic")
                })
                if (sessionPorts.size > 1) {
                    put(JSONObject().apply {
                        put("type", "field")
                        put("network", "tcp,udp")
                        put("balancerTag", "slowdns-balancer")
                    })
                }
            }
            put("rules", rules)
            if (sessionPorts.size > 1) {
                put("balancers", JSONArray().put(JSONObject().apply {
                    put("tag", "slowdns-balancer")
                    put("selector", JSONArray().put("V2RAY_"))
                    put("strategy", JSONObject().apply {
                        put("type", "roundRobin")
                    })
                }))
            }
        }

        return JSONObject().apply {
            put("log", JSONObject().apply {
                put("loglevel", "warning")
            })
            put("inbounds", inbounds)
            put("outbounds", outbounds)
            put("routing", routing)
        }
    }

    private fun startLocalDnsGateway(cfg: JSONObject, onLog: (String) -> Unit) {
        val primaryDns = cfg.optString("custom_dns", "1.1.1.1").ifEmpty { "1.1.1.1" }
        val secondaryDns = cfg.optString("custom_dns_secondary", "8.8.8.8").ifEmpty { "8.8.8.8" }
        val socksPort = cfg.optInt("sharenet_socks_port", 10808)

        // 1. Start Local BadVPN UDPGW Server on 127.0.0.1:7300 (handles all DNS & UDP frames from libtun2socks.so!)
        try {
            try { udpgwLocalServer?.close() } catch (ignored: Exception) {}
            val ugwSrv = ServerSocket()
            ugwSrv.reuseAddress = true
            ugwSrv.bind(InetSocketAddress("127.0.0.1", 7300))
            udpgwLocalServer = ugwSrv
            pool.execute {
                while (running.get() && !ugwSrv.isClosed) {
                    try {
                        val sock = ugwSrv.accept()
                        sock.tcpNoDelay = true
                        pool.execute {
                            sock.use { s ->
                                handleLocalUdpGwStream(
                                    DataInputStream(s.getInputStream()),
                                    s.getOutputStream(),
                                    primaryDns,
                                    secondaryDns,
                                    socksPort
                                )
                            }
                        }
                    } catch (ignored: Exception) {}
                }
            }
        } catch (e: Exception) {
            onLog("Local UDPGW bind note: ${e.message}")
        }

        // 2. Also keep raw UDP DNS listener on 127.0.0.1:8091
        try {
            val udpSock = DatagramSocket(null)
            udpSock.reuseAddress = true
            udpSock.bind(InetSocketAddress("127.0.0.1", LOCAL_DNS_GW_PORT))
            dnsGatewaySocket = udpSock
            onLog("DNS & UDPGW Engine ready (127.0.0.1:7300 / :$LOCAL_DNS_GW_PORT -> $primaryDns, $secondaryDns)")

            pool.execute {
                val buf = ByteArray(2048)
                while (running.get() && !udpSock.isClosed) {
                    try {
                        val pkt = DatagramPacket(buf, buf.size)
                        udpSock.receive(pkt)
                        val queryBytes = pkt.data.copyOfRange(pkt.offset, pkt.offset + pkt.length)
                        val clientAddr = pkt.address
                        val clientPort = pkt.port
                        pool.execute {
                            val resp = resolveDnsQuery(queryBytes, primaryDns, secondaryDns, socksPort)
                            if (resp != null && !udpSock.isClosed) {
                                try {
                                    udpSock.send(DatagramPacket(resp, resp.size, clientAddr, clientPort))
                                } catch (ignored: Exception) {}
                            }
                        }
                    } catch (ignored: Exception) {}
                }
            }
        } catch (e: Exception) {
            onLog("DNS Gateway bind warning: ${e.message}")
        }
    }

    /**
     * Native Kotlin implementation of BadVPN's UDPGW protocol (127.0.0.1:7300) for libtun2socks.so!
     * Intercepts DNS queries (port 53 / 8091 / FLAG_DNS), suppresses QUIC (UDP 443), and forwards UDP packets.
     */
    private fun handleLocalUdpGwStream(
        inp: DataInputStream,
        out: OutputStream,
        primaryDns: String,
        secondaryDns: String,
        socksPort: Int
    ) {
        val writeLock = Any()
        try {
            while (running.get()) {
                val b0 = inp.read()
                if (b0 < 0) break
                val b1 = inp.read()
                if (b1 < 0) break
                val frameLen = (b0 and 0xFF) or ((b1 and 0xFF) shl 8)
                if (frameLen <= 0 || frameLen > 65535) break

                val frame = ByteArray(frameLen)
                inp.readFully(frame)
                if (frameLen < 3) continue

                val flags = frame[0].toInt() and 0xFF
                // Keepalive flag (0x01)
                if ((flags and 0x01) != 0) continue

                val conId0 = frame[1]
                val conId1 = frame[2]
                val isIpv6 = (flags and 0x08) != 0
                val addrSize = if (isIpv6) 16 else 4
                val headerLen = 3 + addrSize + 2
                if (frameLen < headerLen) continue

                val addrBytes = frame.copyOfRange(3, 3 + addrSize)
                val portHi = frame[3 + addrSize].toInt() and 0xFF
                val portLo = frame[3 + addrSize + 1].toInt() and 0xFF
                val dstPort = (portHi shl 8) or portLo
                val payload = frame.copyOfRange(headerLen, frameLen)

                // Drop QUIC (UDP 443) immediately so apps fall back to TCP 443 without stalling
                if (dstPort == 443) continue

                val isDns = (flags and 0x04) != 0 || dstPort == 53 || dstPort == LOCAL_DNS_GW_PORT
                pool.execute {
                    try {
                        val respPayload: ByteArray? = if (isDns) {
                            resolveDnsQuery(payload, primaryDns, secondaryDns, socksPort)
                        } else if (!isIpv6) {
                            // Forward general UDP packet (e.g. NTP 123, STUN/WhatsApp call, games)
                            var uSock: DatagramSocket? = null
                            try {
                                uSock = DatagramSocket()
                                uSock.soTimeout = 2500
                                val targetInet = InetAddress.getByAddress(addrBytes)
                                uSock.send(DatagramPacket(payload, payload.size, targetInet, dstPort))
                                val rBuf = ByteArray(4096)
                                val rPkt = DatagramPacket(rBuf, rBuf.size)
                                uSock.receive(rPkt)
                                rPkt.data.copyOfRange(0, rPkt.length)
                            } catch (ignored: Throwable) {
                                null
                            } finally {
                                try { uSock?.close() } catch (ignored: Throwable) {}
                            }
                        } else {
                            null
                        }

                        if (respPayload != null && respPayload.isNotEmpty()) {
                            val outFrameLen = headerLen + respPayload.size
                            val outPacket = ByteArray(2 + outFrameLen)
                            outPacket[0] = (outFrameLen and 0xFF).toByte()
                            outPacket[1] = ((outFrameLen shr 8) and 0xFF).toByte()
                            outPacket[2] = (if (isIpv6) 0x08 else 0x00).toByte()
                            outPacket[3] = conId0
                            outPacket[4] = conId1
                            System.arraycopy(frame, 3, outPacket, 5, addrSize + 2)
                            System.arraycopy(respPayload, 0, outPacket, 2 + headerLen, respPayload.size)
                            synchronized(writeLock) {
                                out.write(outPacket)
                                out.flush()
                            }
                        }
                    } catch (ignored: Throwable) {}
                }
            }
        } catch (ignored: Throwable) {}
    }

    private val inFlightDnsLocks = ConcurrentHashMap<String, Any>()

    private fun extractDnsCacheKey(query: ByteArray): String? {
        if (query.size <= 12) return null
        return Base64.encodeToString(query, 12, query.size - 12, Base64.NO_WRAP)
    }

    /**
     * Parses the QTYPE of the first DNS question in a DNS packet.
     * Returns 28 for AAAA (IPv6), 65 for HTTPS/SVCB (HTTP/3 QUIC hint), 1 for A (IPv4), etc.
     */
    private fun extractDnsQType(query: ByteArray): Int {
        if (query.size < 17) return -1
        var pos = 12
        while (pos < query.size) {
            val len = query[pos].toInt() and 0xFF
            if (len == 0) {
                pos += 1
                break
            }
            if ((len and 0xC0) == 0xC0) {
                pos += 2
                break
            }
            pos += 1 + len
        }
        if (pos + 4 > query.size) return -1
        return ((query[pos].toInt() and 0xFF) shl 8) or (query[pos + 1].toInt() and 0xFF)
    }

    /**
     * Builds an instant synthetic NOERROR empty DNS response (0 answers) so apps do not
     * waste tunnel bandwidth on IPv6 (AAAA) or hang on HTTP/3 QUIC (HTTPS type 65).
     */
    private fun buildEmptyNoErrorDnsResponse(query: ByteArray): ByteArray {
        val resp = query.clone()
        // QR=1 (response), Opcode=0, AA=0, TC=0, RD=1 -> 0x81
        // RA=1, Z=0, RCODE=0 (NOERROR) -> 0x80
        resp[2] = 0x81.toByte()
        resp[3] = 0x80.toByte()
        // ANCOUNT = 0, NSCOUNT = 0, ARCOUNT = 0
        resp[6] = 0
        resp[7] = 0
        resp[8] = 0
        resp[9] = 0
        resp[10] = 0
        resp[11] = 0
        return resp
    }

    private fun resolveDnsQuery(query: ByteArray, dns1: String, dns2: String, socksPort: Int): ByteArray? {
        if (query.size < 12) return null

        // 0. Immediately return empty NOERROR for IPv6 (AAAA=28) & HTTP/3 QUIC (HTTPS=65, SVCB=64)
        // This cuts DNS load by >50% and forces YouTube/Instagram/TikTok/Chrome onto fast TCP 443!
        val qType = extractDnsQType(query)
        if (qType == 28 || qType == 65 || qType == 64) {
            return buildEmptyNoErrorDnsResponse(query)
        }

        val cacheKey = extractDnsCacheKey(query)
        val now = System.currentTimeMillis()

        // 1. Instant 0.1ms RAM DNS Cache Hit
        if (cacheKey != null) {
            val cached = dnsCache[cacheKey]
            if (cached != null && now < cached.expiryMs && cached.response.size >= 12) {
                val clone = cached.response.clone()
                clone[0] = query[0]
                clone[1] = query[1]
                return clone
            }
        }

        val lockObj = if (cacheKey != null) inFlightDnsLocks.computeIfAbsent(cacheKey) { Any() } else Any()
        synchronized(lockObj) {
            try {
                // Re-check cache after acquiring per-domain lock (deduplicates burst queries from apps!)
                if (cacheKey != null) {
                    val cached = dnsCache[cacheKey]
                    if (cached != null && System.currentTimeMillis() < cached.expiryMs && cached.response.size >= 12) {
                        val clone = cached.response.clone()
                        clone[0] = query[0]
                        clone[1] = query[1]
                        return clone
                    }
                }

                // 2. Fast Direct UDP DNS (450ms timeout) with anti-spoofing check (zero tunnel bandwidth overhead!)
                val udpCandidates = buildList {
                    val slowRes = activeConfig.optString("dns_resolver", "").trim()
                    if (slowRes.isNotEmpty() && !slowRes.startsWith("http") && !slowRes.startsWith("tls") && !slowRes.startsWith("dot")) {
                        add(slowRes.split(":")[0].trim())
                    }
                    add(dns1.split(":")[0].trim())
                    add(dns2.split(":")[0].trim())
                }.distinct().filter { it.isNotEmpty() }

                for (cleanHost in udpCandidates) {
                    var dSock: DatagramSocket? = null
                    try {
                        dSock = DatagramSocket()
                        dSock.soTimeout = 450
                        dSock.send(DatagramPacket(query, query.size, InetAddress.getByName(cleanHost), 53))
                        val rBuf = ByteArray(2048)
                        val rPkt = DatagramPacket(rBuf, rBuf.size)
                        dSock.receive(rPkt)
                        val resp = rPkt.data.copyOfRange(0, rPkt.length)
                        // Verify RCODE == 0 (NOERROR) and ANCOUNT > 0 (not a carrier REFUSED/captive error)
                        val rcode = resp[3].toInt() and 0x0F
                        val ancount = ((resp[6].toInt() and 0xFF) shl 8) or (resp[7].toInt() and 0xFF)
                        if (resp.size >= 16 && rcode == 0 && ancount > 0) {
                            // Verify final 4 bytes of A record are not a private/bogon captive portal IP (10.x, 127.x, 192.168.x, 172.16-31.x)
                            val b0 = resp[resp.size - 4].toInt() and 0xFF
                            val b1 = resp[resp.size - 3].toInt() and 0xFF
                            val isBogon = (b0 == 10) || (b0 == 127) || (b0 == 0) ||
                                (b0 == 192 && b1 == 168) || (b0 == 172 && b1 in 16..31)
                            if (!isBogon) {
                                if (cacheKey != null) {
                                    if (dnsCache.size > 1024) dnsCache.clear()
                                    dnsCache[cacheKey] = CachedDnsEntry(resp.clone(), System.currentTimeMillis() + 600_000L)
                                }
                                return resp
                            }
                        }
                    } catch (ignored: Throwable) {
                    } finally {
                        try { dSock?.close() } catch (ignored: Throwable) {}
                    }
                }

                // 3. Encrypted Tunnel DNS-over-TCP (RFC 1035) through active Xray/V2Ray/SSH tunnel
                for (dnsHost in listOf(dns1, dns2, "8.8.8.8", "1.1.1.1").distinct()) {
                    val cleanHost = dnsHost.split(":")[0].trim()
                    if (cleanHost.isEmpty()) continue
                    try {
                        val tunnelStreams = if (isNativeV2RayActive.get()) {
                            openLocalSocks5Stream(socksPort, cleanHost, 53)
                        } else {
                            openTunnelStream(cleanHost, 53)
                        }
                        if (tunnelStreams != null) {
                            val inp = DataInputStream(tunnelStreams.first)
                            val out = tunnelStreams.second
                            val tcpFrame = ByteArray(query.size + 2)
                            tcpFrame[0] = ((query.size shr 8) and 0xFF).toByte()
                            tcpFrame[1] = (query.size and 0xFF).toByte()
                            System.arraycopy(query, 0, tcpFrame, 2, query.size)
                            out.write(tcpFrame)
                            out.flush()
                            val respLen = inp.readUnsignedShort()
                            val resp = ByteArray(respLen)
                            inp.readFully(resp)
                            try { out.close() } catch (ignored: Throwable) {}
                            try { inp.close() } catch (ignored: Throwable) {}
                            if (cacheKey != null && resp.size >= 12) {
                                if (dnsCache.size > 1024) dnsCache.clear()
                                dnsCache[cacheKey] = CachedDnsEntry(resp.clone(), System.currentTimeMillis() + 600_000L)
                            }
                            return resp
                        }
                    } catch (ignored: Throwable) {}
                }
            } finally {
                if (cacheKey != null) {
                    inFlightDnsLocks.remove(cacheKey)
                }
            }
        }
        return null
    }

    private fun openLocalSocks5Stream(socksPort: Int, targetHost: String, targetPort: Int): Pair<InputStream, OutputStream>? {
        return try {
            val s = Socket()
            s.tcpNoDelay = true
            s.keepAlive = true
            s.soTimeout = 10000
            s.connect(InetSocketAddress("127.0.0.1", socksPort), 5000)
            val inp = DataInputStream(s.getInputStream())
            val out = s.getOutputStream()
            out.write(byteArrayOf(0x05, 0x01, 0x00))
            out.flush()
            if (inp.read() != 0x05 || inp.read() != 0x00) {
                s.close()
                return null
            }
            val hostBytes = targetHost.toByteArray(Charsets.UTF_8)
            val req = ByteArrayOutputStream()
            req.write(byteArrayOf(0x05, 0x01, 0x00, 0x03, hostBytes.size.toByte()))
            req.write(hostBytes)
            req.write((targetPort shr 8) and 0xFF)
            req.write(targetPort and 0xFF)
            out.write(req.toByteArray())
            out.flush()
            val ver = inp.read()
            val rep = inp.read()
            inp.read() // rsv
            val atyp = inp.read()
            if (ver != 0x05 || rep != 0x00) {
                s.close()
                return null
            }
            when (atyp) {
                0x01 -> inp.readFully(ByteArray(4))
                0x03 -> {
                    val l = inp.read()
                    inp.readFully(ByteArray(l))
                }
                0x04 -> inp.readFully(ByteArray(16))
            }
            inp.readUnsignedShort()
            s.soTimeout = 0
            Pair(inp, out)
        } catch (ignored: Exception) {
            null
        }
    }

    private fun nextSlowDnsPort(): Int {
        val ports = dnsttSessionPorts
        if (ports.isEmpty()) return LOCAL_DNSTT_PORT
        val idx = (dnsttRoundRobin.getAndIncrement() and 0x7FFFFFFF) % ports.size
        return ports[idx]
    }

    private fun pickActiveSshSession(): Session? {
        val connected = sshSessionPool.filter { it.isConnected }
        if (connected.isNotEmpty()) {
            val idx = (sshRoundRobin.getAndIncrement() and 0x7FFFFFFF) % connected.size
            return connected[idx]
        }
        val s = sshSession
        return if (s != null && s.isConnected) s else null
    }

    private fun startNativeSlowDnsProcess(cfg: JSONObject, onLog: (String) -> Unit) {
        val ctx = appContext ?: return
        try {
            dnsttProcess?.destroy()
            for (p in dnsttProcesses) {
                try { p.destroy() } catch (ignored: Exception) {}
            }
            dnsttProcesses.clear()
            dnsttSessionPorts.clear()

            val nsDomain = cfg.optString("dnstt_ns", "").trim()
            val pubKey = cfg.optString("dnstt_pubkey", "").trim()
            val resolver = cfg.optString("dns_resolver", "1.1.1.1:53").trim().ifEmpty { "1.1.1.1:53" }
            val sessionCount = cfg.optInt("dnstt_sessions", 4).coerceIn(1, 8)

            if (nsDomain.isEmpty() || pubKey.isEmpty()) {
                onLog("SlowDNS warning: Please set Nameserver (NS) and Public Key in SlowDNS settings!")
                return
            }

            val pubFile = File(ctx.filesDir, "server.pub")
            pubFile.writeText(pubKey + "\n")

            val libDnsFile = File(ctx.applicationInfo.nativeLibraryDir, "libdns.so")
            if (!libDnsFile.exists()) {
                onLog("SlowDNS binary not found at ${libDnsFile.absolutePath}")
                return
            }
            try { libDnsFile.setExecutable(true) } catch (ignored: Throwable) {}

            try { dnsttBalancerServer?.close() } catch (ignored: Exception) {}
            dnsttBalancerServer = null

            onLog("Starting Native SlowDNS ($sessionCount session(s)) -> NS: $nsDomain via $resolver")

            for (idx in 0 until sessionCount) {
                val localPort = LOCAL_DNSTT_PORT + idx
                val cmd = mutableListOf(libDnsFile.absolutePath)
                when {
                    resolver.startsWith("https://", ignoreCase = true) -> {
                        cmd.add("-doh")
                        cmd.add(resolver)
                    }
                    resolver.startsWith("tls://", ignoreCase = true) || resolver.startsWith("dot://", ignoreCase = true) -> {
                        cmd.add("-dot")
                        cmd.add(resolver.substringAfter("://"))
                    }
                    else -> {
                        cmd.add("-udp")
                        val udpTarget = if (resolver.contains(":")) resolver else "$resolver:53"
                        cmd.add(udpTarget)
                    }
                }
                cmd.add("-pubkey-file")
                cmd.add(pubFile.absolutePath)
                cmd.add(nsDomain)
                cmd.add("127.0.0.1:$localPort")

                val pb = ProcessBuilder(cmd)
                pb.redirectErrorStream(true)
                val proc = pb.start()
                if (idx == 0) dnsttProcess = proc
                dnsttProcesses.add(proc)
                dnsttSessionPorts.add(localPort)

                val tag = if (sessionCount > 1) "SlowDNS[#${idx + 1}]" else "SlowDNS"
                pool.execute {
                    try {
                        val reader = BufferedReader(InputStreamReader(proc.inputStream))
                        var line: String?
                        while (reader.readLine().also { line = it } != null) {
                            val l = line?.trim() ?: continue
                            if (l.isNotEmpty()) onLog("$tag: $l")
                        }
                    } catch (ignored: Exception) {}
                }
            }

            Thread.sleep(600)
        } catch (e: Exception) {
            onLog("SlowDNS start error: ${e.message}")
        }
    }

    private fun connectOnce(
        cfg: JSONObject,
        onState: (String, String) -> Unit,
        onLog: (String) -> Unit
    ) {
        val useV2ray = cfg.optBoolean("use_v2ray", false)
        val useSlowDns = cfg.optBoolean("use_slowdns", false)
        val usePayload = cfg.optBoolean("use_payload", false)
        val useSsl = cfg.optBoolean("use_ssl", false)
        val autoReplace = cfg.optBoolean("auto_replace", true)
        val usePsiphon = cfg.optBoolean("use_psiphon", false)

        if (useV2ray) {
            val v2Transport = if (useSlowDns) "V2Ray over SlowDNS" else "V2Ray (${cfg.optString("v2ray_proto", "vless").uppercase()})"
            onLog("Connecting $v2Transport...")
            val testSock = openV2RayTransportSocket(cfg, onLog)
            testSock.close()
            onLog("Connected! $v2Transport active -> starting TUN2SOCKS routing.")
            onState("CONNECTED", v2Transport)

            while (running.get()) {
                Thread.sleep(2000L)
            }
            return
        }

        val host = cfg.optString("server_host", "127.0.0.1")
        val portsStr = cfg.optString("server_ports", "22")
        val candidatePorts = if (useSlowDns) listOf(LOCAL_DNSTT_PORT) else parsePortList(portsStr)
        val user = cfg.optString("ssh_user", "root")
        val pass = cfg.optString("ssh_pass", "")
        val payload = if (usePayload) cfg.optString("payload", "") else ""
        val sni = cfg.optString("sni", "")
        val keepAliveSec = cfg.optInt("keepalive_sec", 45).coerceAtLeast(20)

        var lastErr: Exception? = null
        for (targetPort in candidatePorts) {
            if (!running.get()) return
            try {
                val connectHost = if (useSlowDns) "127.0.0.1" else host
                onLog("Connecting SSH -> $user@$host" + if (useSlowDns) " via SlowDNS (127.0.0.1:$LOCAL_DNSTT_PORT)" else ":$targetPort")
                val jsch = JSch()
                val session = jsch.getSession(user, connectHost, targetPort)
                session.setPassword(pass)

                val props = Properties()
                props["StrictHostKeyChecking"] = "no"
                props["PreferredAuthentications"] = "password,keyboard-interactive"
                // Prioritize hardware-accelerated AEAD/CTR ciphers just like HTTP Custom
                // Prioritize ARMv8 hardware-accelerated AES-GCM / AES-CTR before software ChaCha20
                props["cipher.s2c"] = "aes128-gcm@openssh.com,aes128-ctr,chacha20-poly1305@openssh.com,aes256-ctr"
                props["cipher.c2s"] = "aes128-gcm@openssh.com,aes128-ctr,chacha20-poly1305@openssh.com,aes256-ctr"
                props["compression.s2c"] = "none"
                props["compression.c2s"] = "none"
                session.setConfig(props)
                session.serverAliveInterval = keepAliveSec * 1000
                session.serverAliveCountMax = 3

                session.setSocketFactory(object : SocketFactory {
                    override fun createSocket(tHost: String, tPort: Int): Socket {
                        return buildCustomSshSocket(
                            host = if (useSlowDns) "127.0.0.1" else host,
                            port = tPort,
                            realHost = host,
                            useSlowDns = useSlowDns,
                            useSsl = useSsl,
                            usePayload = usePayload,
                            autoReplace = autoReplace,
                            usePsiphon = usePsiphon,
                            payload = payload,
                            sni = sni,
                            cfg = cfg,
                            onLog = onLog
                        )
                    }
                    override fun getInputStream(socket: Socket): InputStream = socket.getInputStream()
                    override fun getOutputStream(socket: Socket): OutputStream = socket.getOutputStream()
                })

                session.connect(18000)
                sshSession = session
                sshSessionPool.clear()
                sshSessionPool.add(session)

                val slowDnsSessions = if (useSlowDns) cfg.optInt("dnstt_sessions", 4).coerceIn(1, 8) else 1
                if (useSlowDns && slowDnsSessions > 1) {
                    for (sIdx in 1 until slowDnsSessions) {
                        val workerPort = dnsttSessionPorts.getOrElse(sIdx) { LOCAL_DNSTT_PORT }
                        pool.execute {
                            try {
                                if (!running.get()) return@execute
                                val wJsch = JSch()
                                val wSession = wJsch.getSession(user, "127.0.0.1", workerPort)
                                wSession.setPassword(pass)
                                wSession.setConfig(props)
                                wSession.serverAliveInterval = keepAliveSec * 1000
                                wSession.serverAliveCountMax = 3
                                wSession.setSocketFactory(object : SocketFactory {
                                    override fun createSocket(tHost: String, tPort: Int): Socket {
                                        return buildCustomSshSocket(
                                            host = "127.0.0.1",
                                            port = workerPort,
                                            realHost = host,
                                            useSlowDns = true,
                                            useSsl = useSsl,
                                            usePayload = usePayload,
                                            autoReplace = autoReplace,
                                            usePsiphon = usePsiphon,
                                            payload = payload,
                                            sni = sni,
                                            cfg = cfg,
                                            onLog = onLog
                                        )
                                    }
                                    override fun getInputStream(socket: Socket): InputStream = socket.getInputStream()
                                    override fun getOutputStream(socket: Socket): OutputStream = socket.getOutputStream()
                                })
                                wSession.connect(18000)
                                if (running.get()) {
                                    sshSessionPool.add(wSession)
                                    onLog("SlowDNS SSH Session #${sIdx + 1}/$slowDnsSessions active (127.0.0.1:$workerPort)")
                                } else {
                                    wSession.disconnect()
                                }
                            } catch (ignored: Exception) {}
                        }
                    }
                }

                onLog("Local BadVPN UDPGW & DNS Engine active on 127.0.0.1:7300")

                val modeDesc = buildList {
                    add(if (useSlowDns) "SlowDNS(${slowDnsSessions}x)+SSH" else "SSH:$targetPort")
                    if (usePayload) add("Payload")
                    if (useSsl) add("SSL")
                }.joinToString("+")

                onLog("SSH Authenticated ($modeDesc) -> starting TUN2SOCKS routing.")
                onState("CONNECTED", modeDesc)

                while (running.get() && session.isConnected) {
                    Thread.sleep(2000L)
                }
                return
            } catch (e: Exception) {
                lastErr = e
                onLog("SSH attempt failed: ${e.message}")
            }
        }
        throw lastErr ?: Exception("All SSH ports failed ($portsStr)")
    }

    private fun parsePortList(portsStr: String): List<Int> {
        val list = portsStr.split(",", ";", " ")
            .mapNotNull { it.trim().toIntOrNull() }
            .filter { it in 1..65535 }
        return if (list.isNotEmpty()) list else listOf(22, 80, 443)
    }

    private fun buildCustomSshSocket(
        host: String,
        port: Int,
        realHost: String,
        useSlowDns: Boolean,
        useSsl: Boolean,
        usePayload: Boolean,
        autoReplace: Boolean,
        usePsiphon: Boolean,
        payload: String,
        sni: String,
        cfg: JSONObject,
        onLog: (String) -> Unit
    ): Socket {
        val baseSocket = Socket()
        baseSocket.tcpNoDelay = true
        baseSocket.keepAlive = true
        try {
            baseSocket.receiveBufferSize = 262144
            baseSocket.sendBufferSize = 262144
        } catch (ignored: Throwable) {}

        val proxyHost = cfg.optString("proxy_host", "").trim()
        val proxyPort = cfg.optInt("proxy_port", 0)

        when {
            useSlowDns -> {
                val targetSlowDnsPort = if (port in LOCAL_DNSTT_PORT..(LOCAL_DNSTT_PORT + 7)) port else nextSlowDnsPort()
                baseSocket.connect(InetSocketAddress("127.0.0.1", targetSlowDnsPort), 15000)
            }
            proxyHost.isNotEmpty() && proxyPort in 1..65535 -> {
                onLog("Connecting via Remote Proxy $proxyHost:$proxyPort...")
                baseSocket.connect(InetSocketAddress(proxyHost, proxyPort), 12000)
            }
            else -> {
                baseSocket.connect(InetSocketAddress(host, port), 12000)
            }
        }

        val activeSocket: Socket = if (useSsl) {
            val sniHost = sni.ifEmpty { realHost }
            onLog("TLS/SSL Handshake (SNI: $sniHost)...")
            wrapTlsSni(baseSocket, sniHost, port)
        } else {
            baseSocket
        }

        if (usePayload && payload.isNotBlank()) {
            onLog("Injecting HTTP Payload" + if (autoReplace) " (Auto-Replace ON)" else "")
            injectHttpPayload(activeSocket, realHost, port, sni, payload, autoReplace, usePsiphon, onLog)
        }

        return activeSocket
    }

    private fun wrapTlsSni(baseSocket: Socket, sniHost: String, port: Int): SSLSocket {
        val trustAll = arrayOf<TrustManager>(object : X509TrustManager {
            override fun checkClientTrusted(chain: Array<X509Certificate>, authType: String) {}
            override fun checkServerTrusted(chain: Array<X509Certificate>, authType: String) {}
            override fun getAcceptedIssuers(): Array<X509Certificate> = emptyArray()
        })
        val sc = SSLContext.getInstance("TLS")
        sc.init(null, trustAll, SecureRandom())
        val sslSocket = sc.socketFactory.createSocket(baseSocket, sniHost, port, true) as SSLSocket
        val params = SSLParameters()
        if (sniHost.isNotEmpty()) {
            params.serverNames = listOf(SNIHostName(sniHost))
        }
        sslSocket.sslParameters = params
        sslSocket.startHandshake()
        return sslSocket
    }

    private fun injectHttpPayload(
        socket: Socket,
        host: String,
        port: Int,
        sni: String,
        rawPayload: String,
        autoReplace: Boolean,
        usePsiphon: Boolean,
        onLog: (String) -> Unit
    ) {
        val expanded = rawPayload
            .replace("[host_port]", "$host:$port")
            .replace("[host]", host)
            .replace("[port]", port.toString())
            .replace("[sni]", sni.ifEmpty { host })
            .replace("[ua]", "Mozilla/5.0 (Linux; Android 14) AppleWebKit/537.36 Chrome/124.0 Mobile Safari/537.36")
            .replace("[protocol]", "HTTP/1.1")
            .replace("[crlf]", "\r\n")
            .replace("[lf]", "\n")
            .replace("[cr]", "\r")
            .replace("\\r\\n", "\r\n")
            .replace("\\n", "\n")

        val segments = when {
            expanded.contains("[split]") -> expanded.split("[split]")
            expanded.contains("[instant_split]") -> expanded.split("[instant_split]")
            usePsiphon && expanded.length > 24 -> listOf(expanded.substring(0, 16), expanded.substring(16))
            else -> listOf(expanded)
        }

        val out = socket.getOutputStream()
        for (i in segments.indices) {
            val seg = segments[i]
            if (seg.isNotEmpty()) {
                out.write(seg.toByteArray(Charsets.UTF_8))
                out.flush()
            }
            if (i < segments.size - 1) {
                Thread.sleep(75)
            }
        }

        val inp = socket.getInputStream()
        val lineSb = StringBuilder()
        var b: Int
        while (inp.read().also { b = it } != -1) {
            lineSb.append(b.toChar())
            if (b == '\n'.code) break
        }
        val rawStatus = lineSb.toString().trim()
        val displayStatus = if (autoReplace && (rawStatus.contains("101") || rawStatus.contains("200") || rawStatus.startsWith("HTTP/"))) {
            "HTTP/1.1 200 Connection established"
        } else {
            rawStatus
        }
        onLog("Payload response: $displayStatus")

        if (rawStatus.startsWith("HTTP/")) {
            var tail = ""
            while (inp.read().also { b = it } != -1) {
                tail += b.toChar()
                if (tail.endsWith("\r\n\r\n") || tail.endsWith("\n\n") || tail.contains("SSH-2.0")) break
                if (tail.length > 4096) break
            }
        }
    }

    private fun openV2RayTransportSocket(cfg: JSONObject, onLog: (String) -> Unit): Socket {
        val useSlowDns = cfg.optBoolean("use_slowdns", false)
        val v2Host = cfg.optString("v2ray_host", "").ifEmpty { cfg.optString("server_host", "127.0.0.1") }
        val v2Port = cfg.optInt("v2ray_port", 443).let { if (it in 1..65535) it else 443 }
        val v2Tls = cfg.optBoolean("v2ray_tls", true) || cfg.optBoolean("use_ssl", false)
        val v2Sni = cfg.optString("v2ray_sni", "").ifEmpty { cfg.optString("sni", v2Host) }
        val v2Net = cfg.optString("v2ray_net", "ws")
        val v2Path = cfg.optString("v2ray_path", "/").ifEmpty { "/" }

        val rawSock = Socket()
        rawSock.tcpNoDelay = true
        rawSock.keepAlive = true

        if (useSlowDns) {
            val dPort = nextSlowDnsPort()
            onLog("Chaining V2Ray transport over SlowDNS (127.0.0.1:$dPort)...")
            rawSock.connect(InetSocketAddress("127.0.0.1", dPort), 15000)
        } else {
            rawSock.connect(InetSocketAddress(v2Host, v2Port), 12000)
        }

        val transportSock: Socket = if (v2Tls) {
            wrapTlsSni(rawSock, v2Sni.ifEmpty { v2Host }, v2Port)
        } else {
            rawSock
        }

        if (v2Net.equals("ws", ignoreCase = true)) {
            performWebSocketHandshake(transportSock, v2Sni.ifEmpty { v2Host }, v2Path)
        }

        return transportSock
    }

    private fun performWebSocketHandshake(sock: Socket, wsHost: String, wsPath: String) {
        val keyBytes = ByteArray(16)
        rng.nextBytes(keyBytes)
        val secKey = Base64.encodeToString(keyBytes, Base64.NO_WRAP)
        val path = if (wsPath.startsWith("/")) wsPath else "/$wsPath"

        val req = buildString {
            append("GET $path HTTP/1.1\r\n")
            append("Host: $wsHost\r\n")
            append("Upgrade: websocket\r\n")
            append("Connection: Upgrade\r\n")
            append("Sec-WebSocket-Key: $secKey\r\n")
            append("Sec-WebSocket-Version: 13\r\n")
            append("User-Agent: Mozilla/5.0 (Linux; Android 14)\r\n\r\n")
        }
        val out = sock.getOutputStream()
        out.write(req.toByteArray(Charsets.UTF_8))
        out.flush()

        val inp = sock.getInputStream()
        var headerTail = ""
        var b: Int
        while (inp.read().also { b = it } != -1) {
            headerTail += b.toChar()
            if (headerTail.endsWith("\r\n\r\n") || headerTail.endsWith("\n\n")) break
            if (headerTail.length > 4096) break
        }
    }

    private fun openTunnelStream(targetHost: String, targetPort: Int): Pair<InputStream, OutputStream>? {
        if (isNativeV2RayActive.get()) {
            val socksPort = activeConfig.optInt("sharenet_socks_port", 10808)
            return openLocalSocks5Stream(socksPort, targetHost, targetPort)
        }
        val useV2ray = activeConfig.optBoolean("use_v2ray", false)
        if (useV2ray) {
            return openV2RayStream(targetHost, targetPort)
        }

        val s = pickActiveSshSession()
        if (s != null && s.isConnected) {
            return try {
                val ch = s.openChannel("direct-tcpip") as ChannelDirectTCPIP
                ch.setHost(targetHost)
                ch.setPort(targetPort)
                val inp = ch.inputStream
                val out = ch.outputStream
                ch.connect(10000)
                Pair(inp, out)
            } catch (ignored: Exception) {
                null
            }
        }
        return null
    }

    private fun openV2RayStream(targetHost: String, targetPort: Int): Pair<InputStream, OutputStream>? {
        return try {
            val sock = openV2RayTransportSocket(activeConfig, {})
            val proto = activeConfig.optString("v2ray_proto", "vless").lowercase()
            val uuidStr = activeConfig.optString("v2ray_uuid", "").trim()
            val isWs = activeConfig.optString("v2ray_net", "ws").equals("ws", ignoreCase = true)

            val baseIn = sock.getInputStream()
            val baseOut = sock.getOutputStream()

            val wrappedOut: OutputStream = if (isWs) WebSocketClientOutputStream(baseOut, rng) else baseOut
            val wsIn: InputStream = if (isWs) WebSocketClientInputStream(baseIn) else baseIn

            if (proto == "trojan") {
                val header = buildTrojanHeader(uuidStr, targetHost, targetPort)
                wrappedOut.write(header)
                wrappedOut.flush()
                Pair(wsIn, wrappedOut)
            } else {
                val header = buildVlessHeader(uuidStr, targetHost, targetPort)
                wrappedOut.write(header)
                wrappedOut.flush()
                Pair(VlessResponseInputStream(wsIn), wrappedOut)
            }
        } catch (ignored: Exception) {
            null
        }
    }

    private class VlessResponseInputStream(private val delegate: InputStream) : InputStream() {
        private var headerStripped = false

        private fun ensureHeaderStripped() {
            if (!headerStripped) {
                headerStripped = true
                val ver = delegate.read()
                if (ver >= 0) {
                    val addonLen = delegate.read()
                    if (addonLen > 0) {
                        var rem = addonLen
                        val skipBuf = ByteArray(addonLen)
                        while (rem > 0) {
                            val n = delegate.read(skipBuf, 0, rem)
                            if (n <= 0) break
                            rem -= n
                        }
                    }
                }
            }
        }

        override fun read(): Int {
            ensureHeaderStripped()
            return delegate.read()
        }

        override fun read(b: ByteArray, off: Int, len: Int): Int {
            ensureHeaderStripped()
            return delegate.read(b, off, len)
        }

        override fun close() {
            delegate.close()
        }
    }

    private fun buildVlessHeader(uuidStr: String, targetHost: String, targetPort: Int): ByteArray {
        val out = ByteArrayOutputStream()
        out.write(0x00)
        val uuid = try {
            UUID.fromString(uuidStr)
        } catch (ignored: Exception) {
            UUID.nameUUIDFromBytes(uuidStr.toByteArray(Charsets.UTF_8))
        }
        val bb = ByteBuffer.allocate(16)
        bb.putLong(uuid.mostSignificantBits)
        bb.putLong(uuid.leastSignificantBits)
        out.write(bb.array())
        out.write(0x00)
        out.write(0x01)
        out.write((targetPort shr 8) and 0xFF)
        out.write(targetPort and 0xFF)
        val hostBytes = targetHost.toByteArray(Charsets.UTF_8)
        out.write(0x02)
        out.write(hostBytes.size and 0xFF)
        out.write(hostBytes)
        return out.toByteArray()
    }

    private fun buildTrojanHeader(password: String, targetHost: String, targetPort: Int): ByteArray {
        val out = ByteArrayOutputStream()
        val digest = MessageDigest.getInstance("SHA-224").digest(password.toByteArray(Charsets.UTF_8))
        val hexPass = digest.joinToString("") { "%02x".format(it) }
        out.write(hexPass.toByteArray(Charsets.UTF_8))
        out.write("\r\n".toByteArray(Charsets.UTF_8))
        out.write(0x01)
        out.write(0x03)
        val hostBytes = targetHost.toByteArray(Charsets.UTF_8)
        out.write(hostBytes.size and 0xFF)
        out.write(hostBytes)
        out.write((targetPort shr 8) and 0xFF)
        out.write(targetPort and 0xFF)
        out.write("\r\n".toByteArray(Charsets.UTF_8))
        return out.toByteArray()
    }

    private class WebSocketClientOutputStream(
        private val rawOut: OutputStream,
        private val random: SecureRandom
    ) : OutputStream() {
        override fun write(b: Int) {
            write(byteArrayOf(b.toByte()), 0, 1)
        }

        override fun write(b: ByteArray, off: Int, len: Int) {
            if (len <= 0) return
            val frame = ByteArrayOutputStream()
            frame.write(0x82)
            when {
                len <= 125 -> frame.write(0x80 or len)
                len <= 65535 -> {
                    frame.write(0x80 or 126)
                    frame.write((len shr 8) and 0xFF)
                    frame.write(len and 0xFF)
                }
                else -> {
                    frame.write(0x80 or 127)
                    val l = len.toLong()
                    for (shift in 56 downTo 0 step 8) {
                        frame.write(((l shr shift) and 0xFF).toInt())
                    }
                }
            }
            val mask = ByteArray(4)
            random.nextBytes(mask)
            frame.write(mask)
            val maskedPayload = ByteArray(len)
            for (i in 0 until len) {
                maskedPayload[i] = (b[off + i].toInt() xor mask[i % 4].toInt()).toByte()
            }
            frame.write(maskedPayload)
            synchronized(rawOut) {
                rawOut.write(frame.toByteArray())
            }
        }

        override fun flush() {
            synchronized(rawOut) {
                rawOut.flush()
            }
        }

        override fun close() {
            try { rawOut.close() } catch (ignored: Exception) {}
        }
    }

    private class WebSocketClientInputStream(rawIn: InputStream) : InputStream() {
        private val din = DataInputStream(rawIn)
        private var currentFrame: ByteArray = ByteArray(0)
        private var framePos = 0

        override fun read(): Int {
            val one = ByteArray(1)
            val n = read(one, 0, 1)
            return if (n <= 0) -1 else (one[0].toInt() and 0xFF)
        }

        override fun read(b: ByteArray, off: Int, len: Int): Int {
            while (framePos >= currentFrame.size) {
                if (!readNextFrame()) return -1
            }
            val avail = (currentFrame.size - framePos).coerceAtMost(len)
            System.arraycopy(currentFrame, framePos, b, off, avail)
            framePos += avail
            return avail
        }

        private fun readNextFrame(): Boolean {
            return try {
                val b0 = din.readUnsignedByte()
                val opcode = b0 and 0x0F
                if (opcode == 0x08) return false
                val b1 = din.readUnsignedByte()
                val masked = (b1 and 0x80) != 0
                var payloadLen = (b1 and 0x7F).toLong()
                if (payloadLen == 126L) {
                    payloadLen = din.readUnsignedShort().toLong()
                } else if (payloadLen == 127L) {
                    payloadLen = din.readLong()
                }
                val maskKey = ByteArray(4)
                if (masked) din.readFully(maskKey)
                val data = ByteArray(payloadLen.toInt())
                din.readFully(data)
                if (masked) {
                    for (i in data.indices) {
                        data[i] = (data[i].toInt() xor maskKey[i % 4].toInt()).toByte()
                    }
                }
                currentFrame = data
                framePos = 0
                true
            } catch (ignored: Exception) {
                false
            }
        }
    }

    private fun acceptSocks5Loop(server: ServerSocket, onLog: (String) -> Unit) {
        while (running.get() && !server.isClosed) {
            try {
                val client = server.accept()
                pool.execute { handleSocks5Client(client) }
            } catch (ignored: Exception) {}
        }
    }

    private fun handleSocks5Client(client: Socket) {
        try {
            client.tcpNoDelay = true
            try {
                client.receiveBufferSize = 262144
                client.sendBufferSize = 262144
            } catch (ignored: Throwable) {}

            client.use { sock ->
                val inp = DataInputStream(sock.getInputStream())
                val out = sock.getOutputStream()

                val ver = inp.read()
                if (ver != 0x05) return
                val nMethods = inp.read()
                if (nMethods > 0) {
                    val methods = ByteArray(nMethods)
                    inp.readFully(methods)
                }
                out.write(byteArrayOf(0x05, 0x00))
                out.flush()

                val reqVer = inp.read()
                val cmd = inp.read()
                inp.read()
                val atyp = inp.read()
                if (reqVer != 0x05 || cmd != 0x01) return

                val host = when (atyp) {
                    0x01 -> {
                        val ip = ByteArray(4)
                        inp.readFully(ip)
                        InetAddress.getByAddress(ip).hostAddress ?: return
                    }
                    0x03 -> {
                        val len = inp.read()
                        val dom = ByteArray(len)
                        inp.readFully(dom)
                        String(dom, Charsets.UTF_8)
                    }
                    0x04 -> {
                        val ip6 = ByteArray(16)
                        inp.readFully(ip6)
                        InetAddress.getByAddress(ip6).hostAddress ?: return
                    }
                    else -> return
                }
                val port = inp.readUnsignedShort()

                // Intercept BadVPN UDPGW connections (127.0.0.1:7300) from libtun2socks.so directly in-process!
                if (port == 7300 && (host == "127.0.0.1" || host == "localhost")) {
                    out.write(byteArrayOf(0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                    out.flush()
                    val dns1 = activeConfig.optString("custom_dns", "1.1.1.1").ifEmpty { "1.1.1.1" }
                    val dns2 = activeConfig.optString("custom_dns_secondary", "8.8.8.8").ifEmpty { "8.8.8.8" }
                    val sPort = activeConfig.optInt("sharenet_socks_port", 10808)
                    handleLocalUdpGwStream(inp, out, dns1, dns2, sPort)
                    return
                }

                val useV2ray = activeConfig.optBoolean("use_v2ray", false)
                val s = pickActiveSshSession()

                // Zero-Copy High-Speed Path for SSH Direct-TCPIP:
                // Instead of JSch's slow 1KB PipedInputStream and spawning 2 extra threads per socket,
                // bind the client socket's OutputStream directly to ChannelDirectTCPIP!
                if (!useV2ray && s != null && s.isConnected) {
                    val ch = s.openChannel("direct-tcpip") as ChannelDirectTCPIP
                    ch.setHost(host)
                    ch.setPort(port)
                    // JSch pushes decrypted SSH_MSG_CHANNEL_DATA directly to `out` (zero intermediate pipe!)
                    ch.setOutputStream(out, false)
                    val sshOut = ch.outputStream
                    try {
                        ch.connect(10000)
                    } catch (ignored: Throwable) {
                        out.write(byteArrayOf(0x05, 0x04, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                        out.flush()
                        return
                    }
                    out.write(byteArrayOf(0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                    out.flush()

                    val buf = ByteArray(65536)
                    try {
                        var n: Int
                        while (inp.read(buf).also { n = it } > 0) {
                            sshOut.write(buf, 0, n)
                            sshOut.flush()
                        }
                    } catch (ignored: Throwable) {
                    } finally {
                        try { sshOut.close() } catch (ignored: Throwable) {}
                        try { ch.disconnect() } catch (ignored: Throwable) {}
                    }
                    return
                }

                // Fallback / V2Ray stream path
                val remote = openTunnelStream(host, port)
                if (remote == null) {
                    out.write(byteArrayOf(0x05, 0x04, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                    out.flush()
                    return
                }
                out.write(byteArrayOf(0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                out.flush()
                pipeStreams(inp, out, remote.first, remote.second)
            }
        } catch (ignored: Throwable) {}
    }

    fun applyShareNetRuntime(
        enable: Boolean,
        httpPort: Int,
        socksPort: Int,
        onLog: (String) -> Unit
    ) {
        activeConfig.put("enable_sharenet", enable)
        activeConfig.put("sharenet_http_port", httpPort)
        activeConfig.put("sharenet_socks_port", socksPort)
        if (!running.get()) return
        pool.execute {
            if (enable) {
                startShareNetProxyServers(httpPort, socksPort, onLog)
            } else {
                try { httpServer?.close() } catch (ignored: Exception) {}
                try { httpAltServer?.close() } catch (ignored: Exception) {}
                httpServer = null
                httpAltServer = null
                onLog("ShareNet Hotspot Proxy stopped.")
            }
        }
    }

    private fun startShareNetProxyServers(httpPort: Int, socksPort: Int, onLog: (String) -> Unit) {
        try { httpServer?.close() } catch (ignored: Exception) {}
        try { httpAltServer?.close() } catch (ignored: Exception) {}
        httpServer = null
        httpAltServer = null

        try {
            val srv = ServerSocket()
            srv.reuseAddress = true
            srv.bind(InetSocketAddress("0.0.0.0", httpPort))
            httpServer = srv
            pool.execute { acceptHttpShareNetLoop(srv, onLog) }

            // Also bind port 7071 (classic HTTP Custom ShareNet port) if user configured 8080 (or vice-versa)
            val altPort = if (httpPort == 7071) 8080 else 7071
            try {
                val altSrv = ServerSocket()
                altSrv.reuseAddress = true
                altSrv.bind(InetSocketAddress("0.0.0.0", altPort))
                httpAltServer = altSrv
                pool.execute { acceptHttpShareNetLoop(altSrv, onLog) }
            } catch (ignored: Exception) {}

            val hotspotIp = LiteVpnService.getHotspotIpAddress()
            onLog("ShareNet Proxy ACTIVE -> HTTP/SOCKS5: $hotspotIp:$httpPort (also :$altPort & SOCKS5 :$socksPort)")
        } catch (e: Exception) {
            onLog("ShareNet bind error on port $httpPort: ${e.message}")
        }
    }

    private fun acceptHttpShareNetLoop(server: ServerSocket, onLog: (String) -> Unit) {
        while (running.get() && !server.isClosed) {
            try {
                val client = server.accept()
                pool.execute { handleHttpShareNetClient(client) }
            } catch (ignored: Exception) {}
        }
    }

    private fun readAsciiLine(inp: InputStream): String? {
        val sb = StringBuilder(128)
        while (true) {
            val b = inp.read()
            if (b == -1) {
                return if (sb.isEmpty()) null else sb.toString()
            }
            if (b == '\n'.code) break
            if (b != '\r'.code) sb.append(b.toChar())
            if (sb.length > 8192) break
        }
        return sb.toString()
    }

    private fun forwardZeroCopySshOrStream(
        host: String,
        port: Int,
        clientIn: InputStream,
        clientOut: OutputStream
    ) {
        val useV2ray = activeConfig.optBoolean("use_v2ray", false)
        val s = pickActiveSshSession()
        if (!useV2ray && !isNativeV2RayActive.get() && s != null && s.isConnected) {
            val ch = s.openChannel("direct-tcpip") as ChannelDirectTCPIP
            ch.setHost(host)
            ch.setPort(port)
            ch.setOutputStream(clientOut, false)
            val sshOut = ch.outputStream
            ch.connect(10000)
            val buf = ByteArray(65536)
            try {
                var n: Int
                while (clientIn.read(buf).also { n = it } > 0) {
                    sshOut.write(buf, 0, n)
                    sshOut.flush()
                }
            } catch (ignored: Throwable) {
            } finally {
                try { sshOut.close() } catch (ignored: Throwable) {}
                try { ch.disconnect() } catch (ignored: Throwable) {}
            }
            return
        }

        val remote = openTunnelStream(host, port) ?: throw Exception("Tunnel stream unavailable")
        pipeStreams(clientIn, clientOut, remote.first, remote.second)
    }

    private fun handleHttpShareNetClient(client: Socket) {
        try {
            client.tcpNoDelay = true
            client.keepAlive = true
            try {
                client.receiveBufferSize = 262144
                client.sendBufferSize = 262144
            } catch (ignored: Throwable) {}

            val pbIn = PushbackInputStream(client.getInputStream(), 1)
            val firstByte = pbIn.read()
            if (firstByte == -1) {
                client.close()
                return
            }
            pbIn.unread(firstByte)

            // Auto-detect SOCKS5 client on the ShareNet port!
            if (firstByte == 0x05) {
                client.use { sock ->
                    val inp = DataInputStream(pbIn)
                    val out = sock.getOutputStream()
                    val ver = inp.read()
                    if (ver != 0x05) return
                    val nMethods = inp.read()
                    if (nMethods > 0) inp.readFully(ByteArray(nMethods))
                    out.write(byteArrayOf(0x05, 0x00))
                    out.flush()

                    val reqVer = inp.read()
                    val cmd = inp.read()
                    inp.read()
                    val atyp = inp.read()
                    if (reqVer != 0x05 || cmd != 0x01) return
                    val host = when (atyp) {
                        0x01 -> {
                            val ip = ByteArray(4)
                            inp.readFully(ip)
                            InetAddress.getByAddress(ip).hostAddress ?: return
                        }
                        0x03 -> {
                            val len = inp.read()
                            val dom = ByteArray(len)
                            inp.readFully(dom)
                            String(dom, Charsets.UTF_8)
                        }
                        0x04 -> {
                            val ip6 = ByteArray(16)
                            inp.readFully(ip6)
                            InetAddress.getByAddress(ip6).hostAddress ?: return
                        }
                        else -> return
                    }
                    val port = inp.readUnsignedShort()
                    out.write(byteArrayOf(0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0))
                    out.flush()
                    forwardZeroCopySshOrStream(host, port, inp, out)
                }
                return
            }

            // Standard HTTP / HTTPS (CONNECT) Proxy ShareNet handler (byte-exact, zero BufferedReader loss)
            client.use { sock ->
                val out = sock.getOutputStream()
                val reqLine = readAsciiLine(pbIn) ?: return
                val parts = reqLine.trim().split(" ")
                if (parts.size < 2) return
                val method = parts[0]
                val targetUri = parts[1]
                val httpVer = if (parts.size >= 3) parts[2] else "HTTP/1.1"

                val headers = mutableListOf<String>()
                var hostHeader = ""
                while (true) {
                    val line = readAsciiLine(pbIn) ?: break
                    if (line.isEmpty()) break
                    if (line.lowercase().startsWith("host:")) {
                        hostHeader = line.substring(5).trim()
                    }
                    if (line.lowercase().startsWith("proxy-connection:")) {
                        headers.add("Connection: " + line.substringAfter(":").trim())
                    } else if (!line.lowercase().startsWith("proxy-authorization:")) {
                        headers.add(line)
                    }
                }

                if (method.equals("CONNECT", ignoreCase = true)) {
                    val hp = targetUri.split(":")
                    val h = hp[0].trim()
                    val p = if (hp.size > 1) hp[1].trim().toIntOrNull() ?: 443 else 443
                    out.write("HTTP/1.1 200 Connection Established\r\n\r\n".toByteArray(Charsets.UTF_8))
                    out.flush()
                    forwardZeroCopySshOrStream(h, p, pbIn, out)
                } else {
                    var h = ""
                    var p = 80
                    var relativePath = targetUri
                    if (targetUri.startsWith("http://", ignoreCase = true) || targetUri.startsWith("https://", ignoreCase = true)) {
                        try {
                            val u = URI(targetUri)
                            h = u.host ?: ""
                            p = if (u.port > 0) u.port else if (targetUri.startsWith("https://", true)) 443 else 80
                            val rawP = u.rawPath?.ifEmpty { "/" } ?: "/"
                            relativePath = if (u.rawQuery != null) "$rawP?${u.rawQuery}" else rawP
                        } catch (ignored: Exception) {}
                    }
                    if (h.isEmpty()) {
                        val hp = hostHeader.split(":")
                        h = hp[0].trim()
                        p = if (hp.size > 1) hp[1].trim().toIntOrNull() ?: 80 else 80
                    }
                    if (h.isEmpty()) return

                    val remote = openTunnelStream(h, p) ?: return
                    val rebuilt = buildString {
                        append("$method $relativePath $httpVer\r\n")
                        for (hdr in headers) append(hdr).append("\r\n")
                        append("\r\n")
                    }
                    remote.second.write(rebuilt.toByteArray(Charsets.UTF_8))
                    remote.second.flush()
                    pipeStreams(pbIn, out, remote.first, remote.second)
                }
            }
        } catch (ignored: Exception) {}
    }

    private fun pipeStreams(
        cIn: InputStream,
        cOut: OutputStream,
        rIn: InputStream,
        rOut: OutputStream
    ) {
        // Use the thread pool for downstream and current thread for upstream (halves thread creation!)
        val downstreamFuture = pool.submit {
            val buf = ByteArray(65536)
            try {
                var n: Int
                while (rIn.read(buf).also { n = it } > 0) {
                    cOut.write(buf, 0, n)
                    cOut.flush()
                }
            } catch (ignored: Throwable) {
            } finally {
                try { cOut.close() } catch (ignored: Throwable) {}
            }
        }
        val upBuf = ByteArray(65536)
        try {
            var n: Int
            while (cIn.read(upBuf).also { n = it } > 0) {
                rOut.write(upBuf, 0, n)
                rOut.flush()
            }
        } catch (ignored: Throwable) {
        } finally {
            try { rOut.close() } catch (ignored: Throwable) {}
            try { downstreamFuture.get() } catch (ignored: Throwable) {}
        }
    }

    /**
     * Parses vless://, vmess://, or trojan:// links, including Xray Reality (pbk, sid, spx, fp),
     * XTLS Vision (flow=xtls-rprx-vision), and gRPC (type=grpc&serviceName=...)!
     */
    fun parseV2RayLink(uriStr: String): JSONObject? {
        val raw = uriStr.trim()
        return try {
            when {
                raw.startsWith("vless://", ignoreCase = true) || raw.startsWith("trojan://", ignoreCase = true) -> {
                    val proto = if (raw.startsWith("trojan://", true)) "trojan" else "vless"
                    val u = URI(raw)
                    val uuid = u.userInfo ?: ""
                    val host = u.host ?: ""
                    val port = if (u.port > 0) u.port else 443
                    val query = u.rawQuery ?: ""
                    val params = mutableMapOf<String, String>()
                    for (pair in query.split("&")) {
                        val kv = pair.split("=", limit = 2)
                        if (kv.size == 2) params[kv[0]] = java.net.URLDecoder.decode(kv[1], "UTF-8")
                    }
                    val netType = params["type"] ?: "ws"
                    val secType = params["security"] ?: "tls"
                    val pathOrService = if (netType == "grpc") (params["serviceName"] ?: params["path"] ?: "") else (params["path"] ?: "/")
                    JSONObject().apply {
                        put("v2ray_proto", proto)
                        put("v2ray_host", host)
                        put("v2ray_port", port)
                        put("v2ray_uuid", uuid)
                        put("v2ray_net", netType)
                        put("v2ray_path", pathOrService)
                        put("v2ray_sni", params["sni"] ?: params["host"] ?: host)
                        put("v2ray_security", secType)
                        put("v2ray_tls", secType != "none")
                        put("v2ray_flow", params["flow"] ?: "")
                        put("v2ray_fp", params["fp"] ?: "chrome")
                        put("v2ray_pbk", params["pbk"] ?: "")
                        put("v2ray_sid", params["sid"] ?: "")
                        put("v2ray_spx", params["spx"] ?: "/")
                    }
                }
                raw.startsWith("vmess://", ignoreCase = true) -> {
                    val b64 = raw.substring(8).trim()
                    val decoded = String(Base64.decode(b64, Base64.DEFAULT), Charsets.UTF_8)
                    val j = JSONObject(decoded)
                    val host = j.optString("add", "")
                    val port = j.optString("port", "443").toIntOrNull() ?: 443
                    val tlsVal = j.optString("tls", "")
                    JSONObject().apply {
                        put("v2ray_proto", "vmess")
                        put("v2ray_host", host)
                        put("v2ray_port", port)
                        put("v2ray_uuid", j.optString("id", ""))
                        put("v2ray_net", j.optString("net", "ws"))
                        put("v2ray_path", j.optString("path", "/"))
                        put("v2ray_sni", j.optString("sni", j.optString("host", host)))
                        put("v2ray_security", if (tlsVal == "tls") "tls" else "none")
                        put("v2ray_tls", tlsVal == "tls")
                    }
                }
                else -> null
            }
        } catch (ignored: Exception) {
            null
        }
    }
}
