package com.github.javaparser.ast.body;

/**
 * Element with a declaration representable as a String.
 *
 * @author Federico Tomassetti
 * @since July 2014
 */
public interface WithDeclaration {

    /**
     * As {@link WithDeclaration#getDeclarationAsString(boolean, boolean)} including
     * both the modifiers and the throws clause.
     */
    String getDeclarationAsString();

    /**
     * A simple representation of the element declaration.
     * It should fit one string.
     * @param includingModifiers flag to include the modifiers (if present) in the string produced
     * @param includingThrows flag to include the throws clause (if present) in the string produced
     */
    String getDeclarationAsString(boolean includingModifiers, boolean includingThrows);
}
