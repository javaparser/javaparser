package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
class StatCommand : CliktCommand(name = "stat") {
    override fun help(context: Context): String {
        return "Print statistics on JML specification"
    }

    override fun run() {
        TODO("Not yet implemented")
    }
}
