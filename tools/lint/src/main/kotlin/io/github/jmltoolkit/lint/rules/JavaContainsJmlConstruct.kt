package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.Jmlish
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.jml.clauses.JmlContract
import com.github.javaparser.ast.jml.stmt.JmlStatement
import com.github.javaparser.ast.validator.ProblemReporter
import java.util.function.Predicate

/**
 * @author Alexander Weigl
 * @version 1 (19.02.22)
 */
class JavaContainsJmlConstruct : com.github.javaparser.ast.validator.Validator {
    override fun accept(node: Node, problemReporter: ProblemReporter) {
        accept(node, false, problemReporter)
    }

    private fun accept(current: Node, inJml: Boolean, problemReporter: ProblemReporter) {
        val openJml: Predicate<Node> = Predicate<Node> { it: Node? -> it is JmlStatement || it is JmlContract}

        if (!inJml && (current is Jmlish) && !openJml.test(current)) {
            problemReporter.report(current, "Jml construct used in Java part")
            return
        }

        for (it in current.childNodes) {
            accept(it, inJml || openJml.test(current), problemReporter)
        }
    }
}
