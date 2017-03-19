package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java7Validator extends Validators {
    public Java7Validator() {
        super(
                new Java6Validator()
        );
    }
}
