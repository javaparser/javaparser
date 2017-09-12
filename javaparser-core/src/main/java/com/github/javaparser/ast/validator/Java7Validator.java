package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.TryStmt;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java7Validator extends Java6Validator {
    protected final SingleNodeTypeValidator<TryStmt> tryWithLimitedResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty()
                && n.getResources().isEmpty()
                && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, "Try has no finally, no catch, and no resources.");
        }
        for (Expression resource : n.getResources()) {
            if (!(resource instanceof VariableDeclarationExpr)) {
                reporter.report(n, "Try with resources only supports variable declarations.");
            }
        }
    });

    public Java7Validator() {
        super();
        remove(genericsWithoutDiamondOperator);
        replace(tryWithoutResources, tryWithLimitedResources);
        remove(noStringsInSwitch);
        remove(noBinaryIntegerLiterals);
        remove(noUnderscoresInIntegerLiterals);
        remove(noMultiCatch);
    }
}
