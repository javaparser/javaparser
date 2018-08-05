package com.github.javaparser.symbolsolver.resolution.naming;

/**
 * Each Name can be part either of a Declaration or a Reference to a Declaration.
 */
public enum NameRole {
    DECLARATION,
    REFERENCE
}
