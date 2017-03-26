package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 1.4 syntax rules.
 */
public class Java1_4Validator extends Java1_3Validator {
    public Java1_4Validator() {
        super();
        remove(noAssertKeyword);
    }
}
