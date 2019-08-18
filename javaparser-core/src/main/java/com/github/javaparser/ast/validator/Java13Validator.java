package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 13 syntax rules.
 */
public class Java13Validator extends Java12Validator {

    public Java13Validator() {
        super();
        remove(noYield);
    }
}
