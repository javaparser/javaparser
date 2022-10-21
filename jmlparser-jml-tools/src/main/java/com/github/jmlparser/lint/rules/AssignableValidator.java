package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.jml.clauses.JmlMultiExprClause;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class AssignableValidator extends LintRuleVisitor {
    @Override
    public void visit(JmlMultiExprClause n, LintProblemReporter arg) {
        if (n.getKind() == JmlClauseKind.ASSIGNABLE ||
                n.getKind() == JmlClauseKind.ASSIGNABLE_REDUNDANTLY) {
            checkFinalFieldsInAssignableClause(n, arg);
        }
    }

    private void checkFinalFieldsInAssignableClause(JmlMultiExprClause n, LintProblemReporter arg) {
        for (Expression e : n.getExpression()) {
            if (e.isNameExpr()) {
                if (e.asNameExpr().getNameAsString().equals("this")) {
                    arg.error(e, "", "This reference is not re-assignable!");
                    continue;
                }
                var value = e.asNameExpr().resolve();
                if (value.isEnumConstant()) {
                    arg.error(e, "", "Enum constants are not re-assignable!");
                } else if (value.isField()) {
                    var ast = value.asField().toAst();
                    if (ast.isPresent() && ast.get().isFinal()) {
                        arg.error(e, "", "This variable is final, so cannot be assigned");
                    }
                }
            } else if (e.isArrayAccessExpr()) {
                //TODO weigl check for array-ness of name expr
                var rtype = e.asArrayAccessExpr().getName().calculateResolvedType();
                if (!rtype.isArray()) {
                    arg.error(e, "Array access to non-array. Calculated type is %s", rtype.describe());
                }
            } else {
                arg.error(e, "Strange expression type found: %s", e.getMetaModel().getTypeName());
            }
        }
    }
}
