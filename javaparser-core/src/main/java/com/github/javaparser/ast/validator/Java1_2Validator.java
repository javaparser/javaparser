package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java1_2Validator extends Validators {
    public Java1_2Validator() {
        super(
                new CommonValidators(),
                new ModifierValidator(true)
        );
    }
}
