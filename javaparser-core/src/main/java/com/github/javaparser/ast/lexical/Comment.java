package com.github.javaparser.ast.lexical;

import java.util.EnumSet;

/**
 * @author Didier Villevalois
 */
public class Comment extends Lexeme {

    private final CommentKind kind;
    private final String image;

    public Comment(CommentKind kind, String image) {
        this.kind = kind;
        this.image = image;
    }

    @Override
    public LexemeKind getLexemeKind() {
        return LexemeKind.COMMENT;
    }

    public CommentKind getCommentKind() {
        return kind;
    }

    @Override
    public boolean is(CommentKind first, CommentKind... rest) {
        return EnumSet.of(first, rest).contains(getCommentKind());
    }

    @Override
    public String image() {
        return image;
    }
}
