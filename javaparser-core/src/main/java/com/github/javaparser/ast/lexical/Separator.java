package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Separator extends Lexeme {

    private final SeparatorKind kind;

    public Separator(SeparatorKind kind) {
        super();
        this.kind = kind;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.SEPARATOR;
    }

    public SeparatorKind getSeparatorKind() {
        return kind;
    }

    @Override
    public boolean is(SeparatorKind first, SeparatorKind... rest) {
        return EnumSet.of(first, rest).contains(getSeparatorKind());
    }

    @Override
    public String image() {
        return kind.image;
    }
}
