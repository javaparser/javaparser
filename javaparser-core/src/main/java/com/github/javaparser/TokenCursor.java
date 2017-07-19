package com.github.javaparser;

import java.util.function.Function;
import java.util.function.Predicate;

public class TokenCursor {
    private JavaToken token;

    public TokenCursor(JavaToken token) {
        this.token = token;
        Position position = token.getRange().begin;
    }

    public TokenCursor cursorUp() {
        return this;
    }

    public TokenCursor endKey() {
        return this;
    }

    public TokenCursor returnKey() {
        return this;
    }

    public TokenCursor indentLikePreviousLine() {
        return this;
    }

    public TokenCursor insert(JavaToken javaToken) {
        return this;
    }

    public TokenCursor findBackwards(Predicate<JavaToken> matcher) {
        return this;
    }

    public TokenCursor deleteToken() {
        return this;
    }

    public TokenCursor replaceToken(Function<JavaToken, JavaToken> replacer) {
        return this;
    }

    public TokenCursor deleteWhitespace() {
        return this;
    }
}
