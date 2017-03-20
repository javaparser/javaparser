package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.CommonValidators;
import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java1_3Validator extends Java1_2Validator {
    public Java1_3Validator() {
        super();
    }
}
