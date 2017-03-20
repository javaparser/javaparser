package com.github.javaparser.ast.validator;

import com.github.javaparser.ast.validator.chunks.ModifierValidator;

/**
 * This validator validates according to Java 7 syntax rules.
 */
public class Java8Validator extends Java7Validator {
    protected final Validator modifiers = new ModifierValidator(true, true);

    public Java8Validator() {
        super();
        replace(modifiersWithoutDefault, modifiers);
        // TODO validate more annotation locations http://openjdk.java.net/jeps/104
        // TODO validate repeating annotations http://openjdk.java.net/jeps/120
        // TODO validate default interface methods
    }
}
