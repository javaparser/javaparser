package com.github.javaparser.ast.lexical;

/**
* @author Didier Villevalois
*/
public enum LiteralKind {
    LONG,
    INTEGER,
    DECIMAL,
    HEX,
    OCTAL,
    BINARY,
    FLOATING_POINT,
    DECIMAL_FLOATING_POINT,
    HEXADECIMAL_FLOATING_POINT,
    DECIMAL_EXPONENT,
    HEXADECIMAL_EXPONENT,
    CHARACTER,
    STRING,
    // Keep the last comma
    ;
}
