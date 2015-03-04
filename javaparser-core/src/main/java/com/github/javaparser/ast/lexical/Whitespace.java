package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Whitespace extends Lexeme {

    private final WhitespaceKind kind;
    private final String image;

    public Whitespace(WhitespaceKind kind, String image) {
        this.kind = kind;
        this.image = image;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.WHITESPACE;
    }

    public WhitespaceKind getWhitespaceKind() {
        return kind;
    }

    @Override
    public boolean is(WhitespaceKind first, WhitespaceKind... rest) {
        return EnumSet.of(first, rest).contains(getWhitespaceKind());
    }

    @Override
    public String image() {
        return image;
    }
}
