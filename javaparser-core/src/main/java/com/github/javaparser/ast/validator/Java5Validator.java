package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java5Validator extends Validators {
    public Java5Validator() {
        super(
                new CommonValidators(),
                new ModifierValidator()
        );
    }
}
