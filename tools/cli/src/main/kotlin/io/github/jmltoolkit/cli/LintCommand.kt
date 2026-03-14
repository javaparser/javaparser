package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
class LintCommand :
    CliktCommand(name = "lint") {
    override fun help(context: Context): String =
        "Submit usage for a given customer and subscription, accepts one usage item"


    override fun run() {
        TODO("Not yet implemented")
    }
}
