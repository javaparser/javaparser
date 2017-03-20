package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 5 syntax rules.
 */
public class Java5Validator extends Java1_4Validator {
    public Java5Validator() {
        super();
        // TODO validate generics
        // TODO validate "no diamond operator"
        // TODO validate annotations on classes, fields and methods but nowhere else
        // TODO validate enums
        // TODO validate varargs
        // TODO validate for-each
        // TODO validate static imports
    }
}
