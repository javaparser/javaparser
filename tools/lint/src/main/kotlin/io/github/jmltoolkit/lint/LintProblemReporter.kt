package io.github.jmltoolkit.lint

import com.github.javaparser.TokenRange
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange
import java.util.function.Consumer

/**
 * @author Alexander Weigl
 * @version 1 (13.10.22)
 */
class LintProblemReporter(private val problemConsumer: Consumer<LintProblem>) {

    fun warn(node: NodeWithTokenRange<*>, category: String?, ruleId: String, message: String, vararg args: Any?) {
        report(LintRule.WARN, node.tokenRange.orElse(null), category, ruleId, message, args)
    }

    fun hint(node: NodeWithTokenRange<*>, category: String?, ruleId: String, message: String, vararg args: Any?) {
        report(LintRule.HINT, node.tokenRange.orElse(null), category, ruleId, message, args)
    }

    fun error(node: NodeWithTokenRange<*>, category: String?, ruleId: String, message: String, vararg args: Any?) {
        report(LintRule.ERROR, node.tokenRange.orElse(null), category, ruleId, message, args)
    }

    fun report(
        level: String,
        range: TokenRange?,
        category: String?,
        ruleId: String,
        message: String,
        vararg args: Any?
    ) {
        problemConsumer.accept(LintProblem(level, message.format(args), range, null, category, ruleId))
    }

    fun report(lintProblem: LintProblem) {
        problemConsumer.accept(lintProblem)
    }
}

