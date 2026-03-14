package io.github.jmltoolkit.lint

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.visitor.VoidVisitorAdapter

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
abstract class LintRuleVisitor : VoidVisitorAdapter<LintProblemReporter>(), LintRule {
    /**
     * A validator that uses a visitor for validation.
     * This class is the visitor too.
     * Implement the "visit" methods you want to use for validation.
     */
    override fun accept(node: Node, problemReporter: LintProblemReporter, config: JmlLintingConfig) {
        reset()
        node.accept(this, problemReporter)
    }

    protected open fun reset() {
    }
}
