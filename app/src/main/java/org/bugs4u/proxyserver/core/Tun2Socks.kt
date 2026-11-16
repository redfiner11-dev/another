package org.bugs4u.proxyserver.core

import android.os.ParcelFileDescriptor
import java.util.concurrent.atomic.AtomicBoolean

object Tun2Socks {
    private var isLoaded = false
    private val isNativeRunning = AtomicBoolean(false)
    private val lock = Any()
    var logCallback: ((String) -> Unit)? = null

    private fun ensureLoaded() {
        synchronized(lock) {
            if (!isLoaded) {
                System.loadLibrary("tun2socks")
                isLoaded = true
            }
        }
    }

    @JvmStatic
    fun Start(
        vpnInterfaceFileDescriptor: ParcelFileDescriptor?,
        vpnInterfaceMTU: Int,
        vpnIpAddress: String,
        vpnNetMask: String,
        socksServerAddress: String,
        udpgwServerAddress: String,
        dnsgwServerAddress: String,
        udpgwTransparentDNS: Boolean
    ) {
        if (vpnInterfaceFileDescriptor == null) return
        ensureLoaded()

        // Ensure any previous native loop has completely exited before starting a new one
        if (isNativeRunning.get()) {
            Stop()
            var waited = 0
            while (isNativeRunning.get() && waited < 1500) {
                try { Thread.sleep(50) } catch (ignored: InterruptedException) {}
                waited += 50
            }
        }

        val fd = try {
            vpnInterfaceFileDescriptor.detachFd()
        } catch (ignored: Throwable) {
            return
        }

        isNativeRunning.set(true)
        try {
            runTun2Socks(
                fd,
                vpnInterfaceMTU,
                vpnIpAddress,
                vpnNetMask,
                socksServerAddress,
                udpgwServerAddress,
                dnsgwServerAddress,
                if (udpgwTransparentDNS) 1 else 0
            )
        } catch (t: Throwable) {
            logCallback?.invoke("tun2socks exit: ${t.message}")
        } finally {
            isNativeRunning.set(false)
        }
    }

    @JvmStatic
    fun Stop() {
        try {
            if (isLoaded && isNativeRunning.get()) {
                terminateTun2Socks()
            }
        } catch (ignored: Throwable) {}
    }

    @JvmStatic
    fun isRunning(): Boolean = isNativeRunning.get()

    @JvmStatic
    fun logTun2Socks(level: String?, channel: String?, msg: String?) {
        if (level == "ERROR" && !msg.isNullOrBlank()) {
            logCallback?.invoke("tun2socks: $msg")
        }
    }

    @JvmStatic
    private external fun runTun2Socks(
        vpnInterfaceFileDescriptor: Int,
        vpnInterfaceMTU: Int,
        vpnIpAddress: String,
        vpnNetMask: String,
        socksServerAddress: String,
        udpgwServerAddress: String,
        dnsgwServerAddress: String,
        udpgwTransparentDNS: Int
    ): Int

    @JvmStatic
    private external fun terminateTun2Socks(): Int
}
