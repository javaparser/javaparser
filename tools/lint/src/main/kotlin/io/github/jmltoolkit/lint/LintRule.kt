package io.github.jmltoolkit.lint

import com.github.javaparser.ast.Node

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
interface LintRule {
    fun accept(node: Node, problemReporter: LintProblemReporter, config: JmlLintingConfig)

    companion object {
        const val HINT: String = "HINT"
        const val WARN: String = "WARN"
        const val ERROR: String = "ERROR"
    }
}
