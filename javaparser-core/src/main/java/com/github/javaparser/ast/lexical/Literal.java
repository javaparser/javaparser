package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Literal extends Lexeme {

    private final LiteralKind kind;
    private final String image;

    public Literal(LiteralKind kind, String image) {
        this.kind = kind;
        this.image = image;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.LITERAL;
    }

    public LiteralKind getLiteralKind() {
        return kind;
    }

    @Override
    public boolean is(LiteralKind first, LiteralKind... rest) {
        return EnumSet.of(first, rest).contains(getLiteralKind());
    }

    @Override
    public String image() {
        return image;
    }
}
