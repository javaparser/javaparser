package com.github.javaparser;

public class TokenCursor {
    private JavaToken token;

    public TokenCursor(JavaToken token) {
        this.token = token;
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
}
