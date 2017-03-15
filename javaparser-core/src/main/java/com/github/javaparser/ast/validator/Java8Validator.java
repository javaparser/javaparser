package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 8 syntax rules.
 */
public class Java8Validator extends Validators {
    public Java8Validator() {
        super(
                new BaseJavaValidator()
        );
    }
}
