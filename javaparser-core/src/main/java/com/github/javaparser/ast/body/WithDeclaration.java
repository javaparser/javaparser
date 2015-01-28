package com.github.javaparser.ast.body;

/**
 * Element with a declaration representable as a String.
 *
 * @author Federico Tomassetti
 * @since July 2014
 */
public interface WithDeclaration {

    /**
     * As {@link WithDeclaration#getDeclarationAsString(boolean, boolean, boolean)} including
     * the modifiers, the throws clause and the parameters with both type and name.
     * @return String representation of declaration
     */
    String getDeclarationAsString();

    /**
     * As {@link WithDeclaration#getDeclarationAsString(boolean, boolean, boolean)} including
     * the parameters with both type and name.
     * @param includingModifiers flag to include the modifiers (if present) in the string produced
     * @param includingThrows flag to include the throws clause (if present) in the string produced
     * @return String representation of declaration based on parameter flags
     */
    String getDeclarationAsString(boolean includingModifiers, boolean includingThrows);

    /**
     * A simple representation of the element declaration.
     * It should fit one string.
     * @param includingModifiers flag to include the modifiers (if present) in the string produced
     * @param includingThrows flag to include the throws clause (if present) in the string produced
     * @param includingParameterName flag to include the parameter name (while the parameter type is always included) in the string produced
     * @return String representation of declaration based on parameter flags
     */
    String getDeclarationAsString(boolean includingModifiers, boolean includingThrows, boolean includingParameterName);
}
