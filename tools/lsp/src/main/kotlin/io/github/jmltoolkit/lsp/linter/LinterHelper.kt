package io.github.jmltoolkit.lsp.linter

import com.github.javaparser.ast.Node
import io.github.jmltoolkit.lint.JmlLintingConfig
import io.github.jmltoolkit.lint.JmlLintingFacade
import io.github.jmltoolkit.lint.LintProblem
import io.github.jmltoolkit.lint.LintProblemReporter

/**
 *
 * @author Alexander Weigl
 * @version 1 (21.10.22)
 */
object LinterHelper {
    private val config = JmlLintingConfig()
    private val linters = JmlLintingFacade(config).linters

    private val loadedFolders = mutableSetOf<String>()

    /*private fun enableFolder(folder: String) {
        if (folder !in loadedFolders) {
            loadedFolders.add(folder)
            val loader = GroovyClassLoader(javaClass.classLoader)
            File(folder).walkTopDown().forEach {
                val clazz = loader.parseClass(it)
                if (clazz.isInstance(LintRule::class.java)) {
                    val instance = clazz.newInstance()
                    linters.add(instance as LintRule?)
                }
            }
        }
    }*/

    fun lint(n: List<Node>): List<LintProblem> {
        val result = arrayListOf<LintProblem>()
        val reporter = LintProblemReporter(result::add)
        for (rule in linters) {
            n.forEach { rule.accept(it, reporter, config) }
        }
        return result
    }
}