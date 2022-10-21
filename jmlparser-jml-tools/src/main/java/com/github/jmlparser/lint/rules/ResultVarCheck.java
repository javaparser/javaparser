package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.jml.clauses.JmlClauseKind;
import com.github.javaparser.ast.jml.clauses.JmlSimpleExprClause;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class ResultVarCheck extends LintRuleVisitor {
    public static final String NO_METHOD_RESULT = "Cannot use \\result here, as this method / constructor does not return anything";
    private boolean inMethodWithNonVoidReturnType = false;
    private boolean inPostCondition = false;

    @Override
    protected void reset() {
        inPostCondition = false;
    }

    @Override
    public void visit(MethodDeclaration n, LintProblemReporter arg) {
        inMethodWithNonVoidReturnType = !n.getType().isVoidType();
        n.getContracts().ifPresent(l -> l.forEach(v -> v.accept(this, arg)));
        inMethodWithNonVoidReturnType = false;
        n.getBody().ifPresent(l -> l.accept(this, arg));
    }

    @Override
    public void visit(JmlSimpleExprClause n, LintProblemReporter arg) {
        inPostCondition = n.getKind() == JmlClauseKind.ENSURES
                || n.getKind() == JmlClauseKind.ENSURES_FREE
                || n.getKind() == JmlClauseKind.ENSURES_REDUNDANTLY
                || n.getKind() == JmlClauseKind.POST
                || n.getKind() == JmlClauseKind.POST_REDUNDANTLY;
        super.visit(n, arg);
        inPostCondition = false;
    }

    @Override
    public void visit(NameExpr n, LintProblemReporter arg) {
        if (n.getNameAsString().equals("\\result")) {
            if (!inPostCondition)
                arg.error(n, "", "Use of \\result in non-post-conditional clause.");
            if (!inMethodWithNonVoidReturnType)
                arg.error(n, "", NO_METHOD_RESULT);
        }
    }
}
