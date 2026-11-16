package com.kurdo.litevpn

import android.app.Notification
import android.app.NotificationChannel
import android.app.NotificationManager
import android.app.PendingIntent
import android.content.Context
import android.content.Intent
import android.net.ConnectivityManager
import android.net.Network
import android.net.NetworkCapabilities
import android.net.NetworkRequest
import android.net.VpnService
import android.os.Build
import android.os.PowerManager
import org.bugs4u.proxyserver.core.Tun2Socks
import org.json.JSONObject
import java.net.Inet4Address
import java.net.NetworkInterface
import java.util.concurrent.atomic.AtomicBoolean

class LiteVpnService : VpnService() {

    companion object {
        const val ACTION_START = "com.kurdo.litevpn.START"
        const val ACTION_STOP = "com.kurdo.litevpn.STOP"
        const val EXTRA_CONFIG_JSON = "config_json"
        const val CHANNEL_ID = "kurdolite_vpn_channel"

        @Volatile
        var isRunning = false
        var statusListener: ((String, String) -> Unit)? = null
        var logListener: ((String) -> Unit)? = null

        fun getHotspotIpAddress(): String {
            var fallbackWlanIp: String? = null
            try {
                val interfaces = NetworkInterface.getNetworkInterfaces()
                while (interfaces.hasMoreElements()) {
                    val iface = interfaces.nextElement()
                    if (!iface.isUp || iface.isLoopback) continue
                    val name = iface.name.lowercase()
                    if (name.startsWith("tun") || name.startsWith("ppp") || name.startsWith("rmnet") || name.startsWith("ccmni")) continue

                    val addrs = iface.inetAddresses
                    while (addrs.hasMoreElements()) {
                        val addr = addrs.nextElement()
                        if (addr is Inet4Address && !addr.isLoopbackAddress) {
                            val ip = addr.hostAddress ?: continue
                            // Prioritize dedicated Hotspot / USB tethering interfaces over client Wi-Fi wlan0
                            if (name.startsWith("ap") || name.startsWith("swlan") || name.startsWith("softap") ||
                                name.startsWith("wlan1") || name.startsWith("wlan2") || name.startsWith("rndis") ||
                                name.startsWith("usb") || name.startsWith("p2p") || ip.startsWith("192.168.43.") ||
                                ip.startsWith("192.168.42.")
                            ) {
                                return ip
                            }
                            if (fallbackWlanIp == null && (name.startsWith("wlan") || name.startsWith("eth") || ip.startsWith("192.168.") || ip.startsWith("10.") || ip.startsWith("172."))) {
                                fallbackWlanIp = ip
                            }
                        }
                    }
                }
            } catch (ignored: Throwable) {}
            return fallbackWlanIp ?: "192.168.43.1"
        }

        fun getAllLocalIpAddresses(): List<String> {
            val result = mutableListOf<String>()
            try {
                val interfaces = NetworkInterface.getNetworkInterfaces()
                while (interfaces.hasMoreElements()) {
                    val iface = interfaces.nextElement()
                    if (!iface.isUp || iface.isLoopback) continue
                    val name = iface.name.lowercase()
                    if (name.startsWith("tun") || name.startsWith("ppp") || name.startsWith("rmnet") || name.startsWith("ccmni")) continue
                    val addrs = iface.inetAddresses
                    while (addrs.hasMoreElements()) {
                        val addr = addrs.nextElement()
                        if (addr is Inet4Address && !addr.isLoopbackAddress) {
                            val ip = addr.hostAddress ?: continue
                            result.add("$ip ($name)")
                        }
                    }
                }
            } catch (ignored: Throwable) {}
            if (result.isEmpty()) result.add("192.168.43.1")
            return result
        }
    }

    private var tun2SocksThread: Thread? = null
    private val stopping = AtomicBoolean(false)
    private var connectivityManager: ConnectivityManager? = null
    private var networkCallback: ConnectivityManager.NetworkCallback? = null
    private var wakeLock: PowerManager.WakeLock? = null

    override fun onCreate() {
        super.onCreate()
        try {
            connectivityManager = getSystemService(Context.CONNECTIVITY_SERVICE) as ConnectivityManager
            registerNetworkCallback()
        } catch (ignored: Throwable) {}
    }

    override fun onStartCommand(intent: Intent?, flags: Int, startId: Int): Int {
        when (intent?.action) {
            ACTION_STOP -> {
                Thread { stopVpnTunnel() }.start()
                return START_NOT_STICKY
            }
            ACTION_START -> {
                val configJson = intent.getStringExtra(EXTRA_CONFIG_JSON) ?: "{}"
                startVpnTunnel(configJson)
            }
        }
        return START_STICKY
    }

    private fun startVpnTunnel(configJson: String) {
        stopping.set(false)
        val cfg = try { JSONObject(configJson) } catch (ignored: Throwable) { JSONObject() }
        val useWakeLock = cfg.optBoolean("use_wakelock", true)
        val enableShareNet = cfg.optBoolean("enable_sharenet", false)

        updateWakeLock(useWakeLock)
        try {
            startForeground(1, buildMinimalNotification("Connecting tunnel..."))
        } catch (ignored: Throwable) {}
        isRunning = true

        Tun2Socks.logCallback = { msg -> logListener?.invoke(msg) }

        TunnelEngine.start(
            context = this,
            configJson = configJson,
            onState = { state, detail ->
                statusListener?.invoke(state, detail)
                if (state == "CONNECTED" && !stopping.get()) {
                    establishTunAndStartTun2Socks(cfg)
                    updateNotification("Connected ($detail)" + if (enableShareNet) " • ShareNet" else "")
                }
            },
            onLog = { line ->
                logListener?.invoke(line)
            }
        )

        if (enableShareNet) {
            val ip = getHotspotIpAddress()
            val httpPort = cfg.optInt("sharenet_http_port", 8080)
            val socksPort = cfg.optInt("sharenet_socks_port", 10808)
            logListener?.invoke("ShareNet Ready -> HTTP: $ip:$httpPort | SOCKS5: $ip:$socksPort")
            tryEnableRootTethering(httpPort)
        }
    }

    /**
     * Establishes the Android VPN TUN interface (169.254.1.1/24) and starts
     * HTTP Custom's native BadVPN libtun2socks.so engine without fdsan double-close!
     */
    @Synchronized
    private fun establishTunAndStartTun2Socks(cfg: JSONObject) {
        if (stopping.get()) return
        if (Tun2Socks.isRunning() && tun2SocksThread?.isAlive == true) return

        try {
            val socksPort = cfg.optInt("sharenet_socks_port", 10808)
            val dns1 = cfg.optString("custom_dns", "8.8.8.8").ifEmpty { "8.8.8.8" }
            val dns2 = cfg.optString("custom_dns_secondary", "8.8.4.4").ifEmpty { "8.8.4.4" }

            val builder = Builder()
                .setSession("HTTP Custom Lite")
                .setMtu(1500)
                .addAddress("169.254.1.1", 24)
                .addRoute("0.0.0.0", 0)

            try { builder.addDnsServer(dns1) } catch (ignored: Throwable) { builder.addDnsServer("8.8.8.8") }
            try { builder.addDnsServer(dns2) } catch (ignored: Throwable) { builder.addDnsServer("8.8.4.4") }

            try {
                builder.addDisallowedApplication(packageName)
            } catch (ignored: Throwable) {}

            val pfd = builder.establish()
            if (pfd == null) {
                logListener?.invoke("ERROR: VpnService.Builder.establish() returned null")
                return
            }
            logListener?.invoke("TUN established (169.254.1.1/24, MTU 1500) -> starting native tun2socks")

            // Do NOT store pfd in a field to be closed later: Tun2Socks.Start detaches the fd
            // and libtun2socks.so closes it in C on exit (preventing Android 10+ fdsan SIGABRT crashes!)
            val t = Thread {
                try {
                    Tun2Socks.Start(
                        pfd,
                        1500,
                        "169.254.1.2",
                        "255.255.255.0",
                        "127.0.0.1:$socksPort",
                        "127.0.0.1:7300",
                        "127.0.0.1:${TunnelEngine.LOCAL_DNS_GW_PORT}",
                        true
                    )
                } catch (e: Throwable) {
                    logListener?.invoke("tun2socks error: ${e.message}")
                }
            }
            t.name = "Tun2SocksThread"
            t.isDaemon = true
            t.start()
            tun2SocksThread = t
        } catch (e: Throwable) {
            logListener?.invoke("Failed to start TUN2SOCKS: ${e.message}")
        }
    }

    private fun updateWakeLock(enable: Boolean) {
        try {
            if (enable) {
                if (wakeLock == null) {
                    val pm = getSystemService(Context.POWER_SERVICE) as PowerManager
                    wakeLock = pm.newWakeLock(PowerManager.PARTIAL_WAKE_LOCK, "KurdoLite::TunnelWakeLock")
                }
                if (wakeLock?.isHeld == false) {
                    wakeLock?.acquire(12 * 60 * 60 * 1000L)
                }
            } else {
                if (wakeLock?.isHeld == true) {
                    wakeLock?.release()
                }
            }
        } catch (ignored: Throwable) {}
    }

    private fun tryEnableRootTethering(proxyPort: Int) {
        Thread {
            try {
                val cmds = arrayOf(
                    "sysctl -w net.ipv4.ip_forward=1",
                    "iptables -t nat -C POSTROUTING -o tun0 -j MASQUERADE || iptables -t nat -A POSTROUTING -o tun0 -j MASQUERADE",
                    "iptables -C FORWARD -o tun0 -j ACCEPT || iptables -I FORWARD -o tun0 -j ACCEPT",
                    "iptables -C FORWARD -i tun0 -j ACCEPT || iptables -I FORWARD -i tun0 -j ACCEPT"
                ).joinToString(" ; ")
                val proc = Runtime.getRuntime().exec(arrayOf("su", "-c", cmds))
                proc.waitFor()
            } catch (ignored: Throwable) {}
        }.start()
    }

    private fun registerNetworkCallback() {
        val request = NetworkRequest.Builder()
            .addCapability(NetworkCapabilities.NET_CAPABILITY_INTERNET)
            .addCapability(NetworkCapabilities.NET_CAPABILITY_NOT_VPN)
            .build()

        val cb = object : ConnectivityManager.NetworkCallback() {
            override fun onAvailable(network: Network) {
                if (isRunning && !stopping.get()) {
                    TunnelEngine.onNetworkHandover { msg -> logListener?.invoke(msg) }
                }
            }
        }
        networkCallback = cb
        try {
            connectivityManager?.registerNetworkCallback(request, cb)
        } catch (ignored: Throwable) {}
    }

    @Synchronized
    private fun stopVpnTunnel() {
        if (stopping.getAndSet(true)) return
        isRunning = false
        updateWakeLock(false)
        try {
            Tun2Socks.Stop()
            tun2SocksThread?.join(1200)
        } catch (ignored: Throwable) {}
        tun2SocksThread = null
        TunnelEngine.stop()
        statusListener?.invoke("DISCONNECTED", "Ready")
        try {
            @Suppress("DEPRECATION")
            stopForeground(true)
        } catch (ignored: Throwable) {}
        try {
            stopSelf()
        } catch (ignored: Throwable) {}
    }

    override fun onRevoke() {
        Thread { stopVpnTunnel() }.start()
        super.onRevoke()
    }

    override fun onDestroy() {
        networkCallback?.let {
            try { connectivityManager?.unregisterNetworkCallback(it) } catch (ignored: Throwable) {}
        }
        stopVpnTunnel()
        super.onDestroy()
    }

    private fun buildMinimalNotification(text: String): Notification {
        val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
        if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            val channel = NotificationChannel(
                CHANNEL_ID,
                "HTTP Custom Tunnel Status",
                NotificationManager.IMPORTANCE_LOW
            )
            nm.createNotificationChannel(channel)
        }
        val pi = PendingIntent.getActivity(
            this, 0, Intent(this, MainActivity::class.java),
            PendingIntent.FLAG_UPDATE_CURRENT or PendingIntent.FLAG_IMMUTABLE
        )
        val builder = if (Build.VERSION.SDK_INT >= Build.VERSION_CODES.O) {
            Notification.Builder(this, CHANNEL_ID)
        } else {
            @Suppress("DEPRECATION")
            Notification.Builder(this)
        }
        return builder
            .setContentTitle("HTTP Custom Lite")
            .setContentText(text)
            .setSmallIcon(android.R.drawable.ic_lock_lock)
            .setContentIntent(pi)
            .setOngoing(true)
            .build()
    }

    private fun updateNotification(text: String) {
        try {
            val nm = getSystemService(Context.NOTIFICATION_SERVICE) as NotificationManager
            nm.notify(1, buildMinimalNotification(text))
        } catch (ignored: Throwable) {}
    }
}
