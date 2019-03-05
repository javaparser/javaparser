package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;
import com.github.javaparser.ast.validator.chunks.UnderscoreKeywordValidator;

/**
 * This validator validates according to Java 9 syntax rules.
 */
public class Java9Validator extends Java8Validator {
    final Validator underscoreKeywordValidator = new UnderscoreKeywordValidator();
    final Validator modifiers = new ModifierValidator(true, true, true);
    final SingleNodeTypeValidator<TryStmt> tryWithResources = new SingleNodeTypeValidator<>(TryStmt.class, (n, reporter) -> {
        if (n.getCatchClauses().isEmpty()
                && n.getResources().isEmpty()
                && !n.getFinallyBlock().isPresent()) {
            reporter.report(n, "Try has no finally, no catch, and no resources.");
        }
    });

    public Java9Validator() {
        super();
        add(underscoreKeywordValidator);
        remove(noModules);
        replace(modifiersWithoutPrivateInterfaceMethods, modifiers);
        replace(tryWithLimitedResources, tryWithResources);
    }
}
