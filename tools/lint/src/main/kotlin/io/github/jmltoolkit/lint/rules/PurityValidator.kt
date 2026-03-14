package com.github.jmlparser.lint.rules

import com.github.javaparser.ast.Modifier
import com.github.javaparser.ast.Node
import com.github.javaparser.ast.expr.AssignExpr
import com.github.javaparser.ast.expr.MethodCallExpr
import com.github.javaparser.ast.expr.UnaryExpr
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers
import com.github.javaparser.ast.visitor.VoidVisitorAdapter
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRuleVisitor
import kotlin.jvm.optionals.getOrNull

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
class PurityValidator : LintRuleVisitor() {
    override fun visit(n: JmlSimpleExprClause, arg: LintProblemReporter) {
        val r = PurityVisitor()
        n.expression.accept(r, null)
        if (r.reason != null) {
            arg.error(r.reason!!, "", "", "Expression in JML clause must be pure." + r.text)
        }
    }


    override fun visit(n: JmlClassExprDeclaration, arg: LintProblemReporter) {
        val r = PurityVisitor()
        n.invariant.accept(r, null)
        if (r.reason != null) {
            arg.error(r.reason!!, "", "", "Expression in JML invariant clause must be pure." + r.text)
        }
    }

    override fun visit(n: JmlExpressionStmt, arg: LintProblemReporter) {
        val r = PurityVisitor()
        n.expression.accept(r, null)
        if (r.reason != null) {
            arg.error(r.reason!!, "", "", "Expression in JML statements must be pure." + r.text)
        }
    }


    private class PurityVisitor : VoidVisitorAdapter<Void?>() {
        var reason: Node? = null
        var text: String? = null

        override fun visit(n: AssignExpr, arg: Void?) {
            reason = n
        }

        override fun visit(n: UnaryExpr, arg: Void?) {
            when (n.operator) {
                UnaryExpr.Operator.POSTFIX_DECREMENT, UnaryExpr.Operator.POSTFIX_INCREMENT -> {
                    reason = n
                    text = "Postfix de-/increment operator found."
                }

                UnaryExpr.Operator.PREFIX_INCREMENT, UnaryExpr.Operator.PREFIX_DECREMENT -> {
                    reason = n
                    text = "Prefix de-/increment operator found"
                }

                else -> n.expression.accept(this, arg)
            }
        }

        override fun visit(n: MethodCallExpr, arg: Void?) {
            val r = n.resolve().toAst().getOrNull()
            val mods = r as? NodeWithModifiers<*>

            if (mods?.hasModifier(Modifier.DefaultKeyword.JML_PURE) == true
                || mods?.hasModifier(Modifier.DefaultKeyword.JML_STRICTLY_PURE) == true
            ) {
                super.visit(n, arg)
            } else {
                reason = n
                text = METHOD_NOT_PURE
            }
        }
    }

    companion object {
        const val METHOD_NOT_PURE: String = "JML expressions should be pure and this method might not be pure"
        const val ASSIGNMENT_NOT_PURE: String = "JML expressions should be pure and assignments are not pure"
    }
}
