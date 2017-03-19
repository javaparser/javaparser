package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java1_1Validator extends Validators {
    public Java1_1Validator() {
        super(
                new Java1_0Validator()
        );
    }
}
