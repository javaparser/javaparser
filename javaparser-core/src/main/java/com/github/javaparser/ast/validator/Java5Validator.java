package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java5Validator extends Validators {
    public Java5Validator() {
        super(
                new Java1_4Validator()
        );
    }
}
