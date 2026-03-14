package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.Context
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import java.io.File

/**
 * @author Alexander Weigl
 * @version 1 (09.04.23)
 */
class J2JCommand :
    CliktCommand("jml2java") {
    override fun help(context: Context): String =
        "Submit usage for a given customer and subscription, accepts one usage item"

    private val outputFolder by option("-o", "--output", help = "Output folder of the Java Files")
        .file()
        .default(File("out"))

    private val jjbmcMode by option("jjbmc", "JBMC mode")
    private val files by argument("FILES").file().multiple()
    override fun run() {
        TODO("Not yet implemented")
    }
}
