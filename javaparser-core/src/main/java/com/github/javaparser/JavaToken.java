package com.github.javaparser;

/**
 * A token from a parsed source file.
 * (Awkwardly named "Java"Token since JavaCC already generates an internal class Token.)
 */
public class JavaToken {
    public final Range range;
    public final int kind;
    public final String text;

    public JavaToken(Range range, int kind, String text) {
        this.range = range;
        this.kind = kind;
        this.text = text;
    }

    public JavaToken(Token token) {
        this(Range.range(token.beginLine, token.beginColumn, token.endLine, token.endColumn), token.kind, token.image);
    }

    public Range getRange() {
        return range;
    }

    public int getKind() {
        return kind;
    }

    public String getText() {
        return text;
    }

    @Override
    public String toString() {
        return text;
    }
}
