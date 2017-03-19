package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java1_3Validator extends Validators {
    public Java1_3Validator() {
        super(
                new Java1_2Validator()
        );
    }
}
