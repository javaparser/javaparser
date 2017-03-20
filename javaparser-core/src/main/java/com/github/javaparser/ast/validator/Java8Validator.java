package com.github.javaparser.ast.validator;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java8Validator extends Java7Validator {
    public Java8Validator() {
        super();
        // TODO validate more annotation locations http://openjdk.java.net/jeps/104
        // TODO validate repeating annotations http://openjdk.java.net/jeps/120
    }
}
