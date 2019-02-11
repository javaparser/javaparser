package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.stmt.SwitchEntry;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.UnionType;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java7Validator extends Java6Validator {
    final SingleNodeTypeValidator<TryStmt> tryWithLimitedResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty()
                && n.getResources().isEmpty()
                && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, "Try has no finally, no catch, and no resources.");
        }
        for (Expression resource : n.getResources()) {
            if (!resource.isVariableDeclarationExpr()) {
                reporter.report(n, "Try with resources only supports variable declarations.");
            }
        }
    });
    private final SingleNodeTypeValidator<UnionType> multiCatch = new SingleNodeTypeValidator<>(UnionType.class, (n, reporter) -> {
        // Case "0 elements" is caught elsewhere.
        if (n.getElements().size() == 1) {
            reporter.report(n, "Union type (multi catch) must have at least two elements.");
        }
    });

    final Validator intAndEnumAndStringSwitch = new SimpleValidator<>(SwitchEntry.class,
            n -> !n.getLabels().stream().allMatch(l -> l.isIntegerLiteralExpr() || l.isNameExpr() || l.isStringLiteralExpr()),
            (n, reporter) -> reporter.report(n.getLabels().getParentNode().get(), "Only 'int's, enums, and strings in switch statements are supported.")
    );

    public Java7Validator() {
        super();
        remove(genericsWithoutDiamondOperator);
        replace(tryWithoutResources, tryWithLimitedResources);
        replace(intAndEnumSwitch, intAndEnumAndStringSwitch);
        remove(noBinaryIntegerLiterals);
        remove(noUnderscoresInIntegerLiterals);
        replace(noMultiCatch, multiCatch);
    }
}
