package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java1_2Validator extends Validators {
    public Java1_2Validator() {
        super(
                new Java1_1Validator()
        );
    }
}
