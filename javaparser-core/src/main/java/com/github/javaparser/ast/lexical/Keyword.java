package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Keyword extends Lexeme {

    private final KeywordKind kind;

    public Keyword(KeywordKind kind) {
        super();
        this.kind = kind;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.KEYWORD;
    }

    public KeywordKind getKeywordKind() {
        return kind;
    }

    @Override
    public boolean is(KeywordKind first, KeywordKind... rest) {
        return EnumSet.of(first, rest).contains(getKeywordKind());
    }

    @Override
    public String image() {
        return kind.image;
    }
}
