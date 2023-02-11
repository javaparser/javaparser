package com.github.jmlparser.lint.rules;

import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.jml.stmt.JmlGhostStmt;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.jmlparser.lint.LintProblemReporter;
import com.github.jmlparser.lint.LintRuleVisitor;

/**
 * @author Alexander Weigl
 * @version 1 (14.10.22)
 */
public class OverridingLocalNamesInGhost extends LintRuleVisitor {
    private boolean inGhost;

    @Override
    protected void reset() {
        inGhost = false;
    }

    @Override
    public void visit(JmlGhostStmt n, LintProblemReporter arg) {
        inGhost = true;
        super.visit(n, arg);
        inGhost = false;
    }

    @Override
    public void visit(VariableDeclarationExpr n, LintProblemReporter arg) {
        if (inGhost) {
            JmlGhostStmt s = n.findAncestor(JmlGhostStmt.class).get();
            for (VariableDeclarator variable : n.getVariables()) {
                var name = variable.getNameAsExpression();
                name.setParentNode(s);
                var value = s.getSymbolResolver().resolveDeclaration(name, ResolvedValueDeclaration.class);
                name.setParentNode(null);
                if (value != null) {
                    arg.error(variable, "", "", "Variable %s already declared in Java.", variable.getNameAsString());
                }
            }
        }
    }
}
