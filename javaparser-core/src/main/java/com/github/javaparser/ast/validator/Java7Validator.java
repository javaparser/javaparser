package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.stmt.TryStmt;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java7Validator extends Java6Validator {
    protected final Validator tryWithResources = new SimpleValidator<>(TryStmt.class,
            n -> n.getCatchClauses().isEmpty()
                    && n.getResources().isEmpty()
                    && !n.getFinallyBlock().isPresent(),
            (n, reporter) -> reporter.report(n, "Try has no finally, no catch, and no resources.")
    );

    public Java7Validator() {
        super();
        remove(genericsWithoutDiamondOperator);
        replace(tryWithoutResources, tryWithResources);
        remove(noStringsInSwitch);
        // TODO validate "binary integer literals"
        // TODO validate "underscores in numeric literals"
        // TODO validate "multi-catch"

    }
}
