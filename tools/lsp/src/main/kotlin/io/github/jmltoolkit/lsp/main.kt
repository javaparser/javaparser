package io.github.jmltoolkit.lsp

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.int
import org.eclipse.lsp4j.launch.LSPLauncher
import org.eclipse.lsp4j.services.LanguageClient
import org.tinylog.Logger
import java.io.InputStream
import java.io.OutputStream
import java.net.InetAddress
import java.net.ServerSocket
import java.net.Socket

/**
 * @author Alexander Weigl
 * @version 1 (10.07.22)
 */
object Main {
    @JvmStatic
    fun main(args: Array<String>) {
        JmlLspCommand().main(args)
    }
}

class JmlLspCommand : CliktCommand() {
    private val mode by option("--mode", "-m").default("client")
    private val port by option("--port", "-p").int()

    override fun run() {
        try {
            when (mode) {
                "server" -> runAsServer()
                "client" -> runAsClient()
                "local" -> launchLanguageServer(System.`in`, System.out)
                else -> require(false) { "Wrong mode given" }
            }
        } catch (e: Exception) {
            Logger.error(e)
        }
    }

    private fun runAsClient() {
        require(port != null)
        val socket = Socket("localhost", port!!)
        launchLanguageServer(socket.getInputStream(), socket.getOutputStream())
    }

    private fun launchLanguageServer(input: InputStream, output: OutputStream) {
        val server = JmlLanguageServer()
        val launcher = LSPLauncher.createServerLauncher(server, input, output)
        val client: LanguageClient = launcher.remoteProxy
        server.connect(client)
        launcher.startListening()
    }

    private fun runAsServer() {
        require(port != null)
        while (true) {
            try {
                ServerSocket(port!!, 1, InetAddress.getLoopbackAddress()).use { serverSocket ->
                    Logger.info("Listening on {}", serverSocket.localSocketAddress)
                    val socket = serverSocket.accept()
                    launchLanguageServer(socket.getInputStream(), socket.getOutputStream())
                }
            } catch (e: Exception) {
                Logger.error(e)
            }
        }
    }

}