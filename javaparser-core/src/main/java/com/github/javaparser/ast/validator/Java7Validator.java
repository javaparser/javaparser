package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java7Validator extends Java6Validator {
    public Java7Validator() {
        super();
        // TODO validate "strings in switch"
        // TODO validate "resource management in try statement"
        // TODO validate "diamond operator"
        // TODO validate "binary integer literals"
        // TODO validate "underscores in numeric literals"
        // TODO validate "multi-catch"

    }
}
