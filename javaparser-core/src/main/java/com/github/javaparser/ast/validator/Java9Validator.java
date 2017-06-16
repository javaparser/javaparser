package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.ModifierValidator;
import com.github.javaparser.ast.validator.chunks.UnderscoreKeywordValidator;

/**
 * This validator validates according to Java 9 syntax rules.
 */
public class Java9Validator extends Java8Validator {
    protected final Validator underscoreKeywordValidator = new UnderscoreKeywordValidator();
    protected final Validator modifiers = new ModifierValidator(true, true, true);

    public Java9Validator() {
        super();
        add(underscoreKeywordValidator);
        remove(noModules);
        replace(modifiersWithoutPrivateInterfaceMethods, modifiers);
    }
}
