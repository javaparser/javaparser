package com.github.javaparser.ast.lexical;

/**
* @author Didier Villevalois
*/
public enum SeparatorKind {
    LPAREN("("),
    RPAREN(")"),
    LBRACE("{"),
    RBRACE("}"),
    LBRACKET("["),
    RBRACKET("]"),
    SEMICOLON(";"),
    COMMA(","),
    DOT("."),
    AT("@"),
    // Keep the last comma
    ;

    public final String image;

    SeparatorKind(String image) {
        this.image = image;
    }
}
