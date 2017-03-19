package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java6Validator extends Validators {
    public Java6Validator() {
        super(
                new Java5Validator()
        );
    }
}
