package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.types.file

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
class PrettyPrintCommand : CliktCommand(name = "format") {
    override fun help(context: Context): String = "Format the JML comments inside Java files."

    private val files by argument("FILES").file().multiple()
    override fun run() {}
}
