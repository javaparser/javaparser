package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.jml.clauses.JmlForallClause
import com.github.javaparser.ast.jml.clauses.JmlSignalsClause
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause
import com.github.javaparser.jml.JmlUtility
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRule
import io.github.jmltoolkit.lint.LintRuleVisitor

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
class JmlNameClashWithJava : LintRuleVisitor() {
    override fun visit(n: JmlSignalsClause, arg: LintProblemReporter) {
        val rtype= n.parameter.type.resolve()
        val exception= JmlUtility.resolveException(n)
        if (exception.isAssignableBy(rtype)) {
            arg.report(NOT_AN_EXCEPTION_CLASS.create(n))
        }
        super.visit(n, arg)
    }


    override fun visit(n: JmlForallClause, arg: LintProblemReporter?) {
        super.visit(n, arg)
    }

    override fun visit(n: JmlSimpleExprClause, arg: LintProblemReporter?) {
        super.visit(n, arg)
    }

    companion object {
        val NOT_AN_EXCEPTION_CLASS
                : LintProblemMeta = LintProblemMeta("JML-1", "This is not an exception class", LintRule.ERROR)

        const val PUT_IN_THROWS_CLAUSE: String =
            "This exception (or a superclass or subclass of it) should be mentioned in the throws clause of this method"

        const val CLASS_REFERENCE_NOT_FOUND: String = "This class could not be resolved, did you forget to import it?"


        const val NOT_A_TYPE_NAME: String = "This is not the name of a primitive type or a class"
        const val NO_ARRAY: String = "This is not an array"
    }
}
