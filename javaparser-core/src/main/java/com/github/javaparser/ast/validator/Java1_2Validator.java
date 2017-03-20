package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 1.2 syntax rules.
 */
public class Java1_2Validator extends Java1_1Validator {
    protected final Validator modifiersWithoutDefault = new ModifierValidator(true, false);

    public Java1_2Validator() {
        super();
        replace(modifiersWithoutStrictfpAndDefault, modifiersWithoutDefault);
    }
}
