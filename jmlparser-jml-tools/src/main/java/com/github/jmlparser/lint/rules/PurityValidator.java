package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.jml.body.JmlClassExprDeclaration;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.validator.ProblemReporter;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (12/29/21)
 */
public class PurityValidator extends LintRuleVisitor {
    public static final String METHOD_NOT_PURE = "JML expressions should be pure and this method might not be pure";
    public static final String ASSIGNMENT_NOT_PURE = "JML expressions should be pure and assignments are not pure";

    @Override
    public void visit(JmlSimpleExprClause n, LintProblemReporter arg) {
        final var r = new PurityVisitor();
        n.getExpression().accept(r, null);
        if (r.reason != null) {
            arg.error(r.reason, "", "Expression in JML clause must be pure." + r.text);
        }
    }


    @Override
    public void visit(JmlClassExprDeclaration n, LintProblemReporter arg) {
        final var r = new PurityVisitor();
        n.getInvariant().accept(r, null);
        if (r.reason != null) {
            arg.error(r.reason, "", "Expression in JML invariant clause must be pure." + r.text);
        }
    }

    @Override
    public void visit(JmlExpressionStmt n, LintProblemReporter arg) {
        final var r = new PurityVisitor();
        n.getExpression().accept(r, null);
        if (r.reason != null) {
            arg.error(r.reason, "", "Expression in JML statements must be pure." + r.text);
        }
    }


    private static class PurityVisitor extends VoidVisitorAdapter<Void> {
        private Node reason;
        private String text;

        @Override
        public void visit(AssignExpr n, Void arg) {
            reason = n;
        }

        @Override
        public void visit(UnaryExpr n, Void arg) {
            switch (n.getOperator()) {
                case POSTFIX_DECREMENT:
                case POSTFIX_INCREMENT:
                    reason = n;
                    text = "Postfix de-/increment operator found.";
                    break;
                case PREFIX_INCREMENT:
                case PREFIX_DECREMENT:
                    reason = n;
                    text = "Prefix de-/increment operator found";
                    break;
                default:
                    n.getExpression().accept(this, arg);
                    break;
            }
        }

        @Override
        public void visit(MethodCallExpr n, Void arg) {
            var r = n.resolve().toAst();
            if (r.isPresent()
                    && (r.get().hasModifier(Modifier.DefaultKeyword.JML_PURE)
                    || r.get().hasModifier(Modifier.DefaultKeyword.JML_STRICTLY_PURE))) {
                super.visit(n, arg);
            } else {
                reason = n;
                text = METHOD_NOT_PURE;
            }
        }
    }
}
