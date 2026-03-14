package io.github.jmltoolkit.cli

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.core.main
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.arguments.argument
import com.github.ajalt.clikt.parameters.arguments.multiple
import com.github.ajalt.clikt.parameters.options.default
import com.github.ajalt.clikt.parameters.options.flag
import com.github.ajalt.clikt.parameters.options.multiple
import com.github.ajalt.clikt.parameters.options.option
import com.github.ajalt.clikt.parameters.types.file
import com.github.ajalt.clikt.parameters.types.int
import com.github.javaparser.JavaParser
import com.github.javaparser.ParseResult
import com.github.javaparser.ParserConfiguration
import com.github.javaparser.Problem
import com.github.javaparser.ast.CompilationUnit
import com.github.javaparser.ast.Node
import io.github.jmltoolkit.lint.JmlLintingConfig
import io.github.jmltoolkit.lint.JmlLintingFacade
import io.github.jmltoolkit.lint.LintProblem
import java.io.File
import java.io.FileNotFoundException
import kotlin.jvm.optionals.getOrNull

fun main(args: Array<String>) {
    var cmd = Main().subcommands(
        J2JCommand(), LintCommand(), PrettyPrintCommand(), XPathCommand(),
        StatCommand(), WdCommand(),
    )
    cmd.main(args)
}

/**
 * @author Alexander Weigl
 * @version 1 (12/31/21)
 */
class Main : CliktCommand() {

    override fun run() {
        TODO("Not yet implemented")
    }
}

abstract class FileBasedCommand(name: String) : CliktCommand(name) {
    val activeJmlKeys by option("--jml-key").multiple()
    val verbose by option("--verbose", "-v", help = "Level of verbosity").int().default(1)
    val disableJml by option("--disable-jml").flag()
    val files by argument("").file().multiple()

    fun lint(nodes: Collection<Node>) {
        val lconfig: JmlLintingConfig = createLinterConfiguration()
        val problems = JmlLintingFacade(lconfig).lint(nodes)
        for (problem in problems) {
            report(problem)
        }
    }

    private fun createLinterConfiguration(): JmlLintingConfig {
        return JmlLintingConfig()
    }

    fun parse(files: List<File>, config: ParserConfiguration): Collection<CompilationUnit> {
        val expanded: MutableList<File> = ArrayList(files.size * 10)
        for (f in files) {
            if (f.isDirectory) {
                expandDirectory(expanded, f)
            } else {
                expanded.add(f)
            }
        }

        return expanded.asSequence().map { parse(it, config) }.map { reportOnError(it) }.filterNotNull().toList()
    }

    private fun reportOnError(it: ParseResult<CompilationUnit>?): CompilationUnit? {
        if (it == null) return null

        val result = it.result.getOrNull()
        if (result != null) return result

        for (problem in it.problems) {
            report(problem)
        }

        return null
    }


    private fun expandDirectory(target: MutableCollection<File>, dir: File) {
        val files = dir.listFiles()
        if (files != null) {
            for (file in files) {
                if (file.isDirectory) {
                    expandDirectory(target, file)
                } else {
                    if (file.name.endsWith(".java")) {
                        target.add(file)
                    }
                }
            }
        }
    }


    internal fun parse(file: File, configuration: ParserConfiguration): ParseResult<CompilationUnit>? {
        val p = JavaParser(configuration)
        try {
            return p.parse(file)
        } catch (e: FileNotFoundException) {
            report(Problem("File not found", null, e))
            return null
        }
    }

    internal fun createParserConfiguration(
        activeJmlKeys: List<String> = listOf(),
        disableJml: Boolean = false
    ): ParserConfiguration {
        val config = ParserConfiguration()
        config.jmlKeys.add(activeJmlKeys)
        config.setProcessJml(disableJml)
        return config
    }


    private fun report(problem: Problem) {
        System.out.println(problem.toString())
    }

    private fun report(problem: LintProblem) {
        println(problem.toString())
    }
}