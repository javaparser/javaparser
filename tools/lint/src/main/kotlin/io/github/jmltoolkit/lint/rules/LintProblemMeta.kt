package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.Node
import com.github.javaparser.ast.nodeTypes.NodeWithTokenRange
import io.github.jmltoolkit.lint.LintProblem

/**
 * @author Alexander Weigl
 * @version 1 (21.10.22)
 */
@JvmRecord
data class LintProblemMeta(val id: String, val message: String, val level: String) {
    fun create(n: NodeWithTokenRange<Node?>): LintProblem {
        return LintProblem(level, message, n.tokenRange.orElse(null), null, id, "")
    }
}
