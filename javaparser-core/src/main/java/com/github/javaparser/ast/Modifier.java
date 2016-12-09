package com.github.javaparser.ast;

import java.util.EnumSet;

public enum Modifier {
    PUBLIC,
    PROTECTED,
    PRIVATE,
    ABSTRACT,
    STATIC,
    FINAL,
    TRANSIENT,
    VOLATILE,
    SYNCHRONIZED,
    NATIVE,
    STRICTFP;

    final String codeRepresentation;

    Modifier() {
        this.codeRepresentation = name().toLowerCase();
    }

    /**
     * @return the keyword represented by this modifier.
     */
    public String asString() {
        return codeRepresentation;
    }

    public EnumSet<Modifier> toEnumSet() {
        return EnumSet.of(this);
    }

    public static AccessSpecifier getAccessSpecifier(EnumSet<Modifier> modifiers) {
        if (modifiers.contains(Modifier.PUBLIC)) {
            return AccessSpecifier.PUBLIC;
        } else if (modifiers.contains(Modifier.PROTECTED)) {
            return AccessSpecifier.PROTECTED;
        } else if (modifiers.contains(Modifier.PRIVATE)) {
            return AccessSpecifier.PRIVATE;
        } else {
            return AccessSpecifier.DEFAULT;
        }
    }
}
