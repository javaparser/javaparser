package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.body.MethodDeclaration
import com.github.javaparser.ast.expr.NameExpr
import com.github.javaparser.ast.jml.clauses.*
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRuleVisitor

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
class ResultVarCheck : LintRuleVisitor() {
    private var inMethodWithNonVoidReturnType = false
    private var inPostCondition = false

    override fun reset() {
        inPostCondition = false
    }

    override fun visit(n: MethodDeclaration, arg: LintProblemReporter) {
        inMethodWithNonVoidReturnType = !n.type.isVoidType
        n.contracts.forEach { v -> v.accept(this, arg) }
        inMethodWithNonVoidReturnType = false
        n.body.ifPresent { l -> l.accept(this, arg) }
    }

    override fun visit(n: JmlSimpleExprClause, arg: LintProblemReporter?) {
        inPostCondition =
            n.kind === JmlClauseKind.ENSURES || n.kind === JmlClauseKind.ENSURES_FREE || n.kind === JmlClauseKind.ENSURES_REDUNDANTLY || n.kind === JmlClauseKind.POST || n.kind === JmlClauseKind.POST_REDUNDANTLY
        super.visit(n, arg)
        inPostCondition = false
    }

    override fun visit(n: NameExpr, arg: LintProblemReporter) {
        if (n.nameAsString.equals("\\result")) {
            if (!inPostCondition) arg.error(n, "", "", "Use of \\result in non-post-conditional clause.")
            if (!inMethodWithNonVoidReturnType) arg.error(n, "", "", NO_METHOD_RESULT)
        }
    }

    companion object {
        const val NO_METHOD_RESULT: String =
            "Cannot use \\result here, as this method / constructor does not return anything"
    }
}
