package io.github.jmltoolkit.lint.rules

import com.github.javaparser.ast.body.FieldDeclaration
import com.github.javaparser.ast.jml.clauses.JmlClauseKind
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause
import io.github.jmltoolkit.lint.LintProblemReporter
import io.github.jmltoolkit.lint.LintRuleVisitor
import kotlin.jvm.optionals.getOrNull

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
class AssignableValidator : LintRuleVisitor() {
    override fun visit(n: JmlMultiExprClause, arg: LintProblemReporter) {
        if (n.kind === JmlClauseKind.ASSIGNABLE ||
            n.kind === JmlClauseKind.ASSIGNABLE_REDUNDANTLY
        ) {
            checkFinalFieldsInAssignableClause(n, arg)
        }
    }

    private fun checkFinalFieldsInAssignableClause(n: JmlMultiExprClause, arg: LintProblemReporter) {
        for (e in n.expression) {
            if (e.isNameExpr) {
                if (e.asNameExpr().nameAsString.equals("this")) {
                    arg.error(e, "", "", "This reference is not re-assignable!")
                    continue
                }
                val value = e.asNameExpr().resolve()
                if (value.isEnumConstant) {
                    arg.error(e, "", "", "Enum constants are not re-assignable!")
                } else if (value.isField) {
                    val ast = value.asField().toAst().getOrNull()
                    if (ast is FieldDeclaration && ast.isFinal) {
                        arg.error(e, "", "", "This variable is final, so cannot be assigned")
                    }
                }
            } else if (e.isArrayAccessExpr) {
                //TODO weigl check for array-ness of name expr
                val rtype = e.asArrayAccessExpr().name.calculateResolvedType()
                if (!rtype.isArray) {
                    arg.error(e, "", "", "Array access to non-array. Calculated type is %s", rtype.describe())
                }
            } else {
                arg.error(e, "", "", "Strange expression type found: %s", e.metaModel.typeName)
            }
        }
    }
}
