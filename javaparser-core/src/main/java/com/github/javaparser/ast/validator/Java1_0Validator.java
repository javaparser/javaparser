package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 1.0 syntax rules.
 */
public class Java1_0Validator extends Validators {
    protected Validator modifiersWithoutStrictfp = new ModifierValidator(false);

    public Java1_0Validator() {
        super(new CommonValidators());
        add(modifiersWithoutStrictfp);
    }
}
