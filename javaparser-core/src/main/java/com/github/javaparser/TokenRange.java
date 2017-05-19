package com.github.javaparser;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * The range of tokens covered by this node.
 */
public class TokenRange {
    public static final TokenRange INVALID = new TokenRange(JavaToken.INVALID, JavaToken.INVALID);
    
    private final JavaToken begin;
    private final JavaToken end;

    public TokenRange(JavaToken begin, JavaToken end) {
        this.begin = assertNotNull(begin);
        this.end = assertNotNull(end);
    }

    public JavaToken getBegin() {
        return begin;
    }

    public JavaToken getEnd() {
        return end;
    }

    public Range getRange() {
        return new Range(begin.getRange().begin, end.getRange().end);
    }

    public TokenRange withBegin(JavaToken begin) {
        return new TokenRange(assertNotNull(begin), end);
    }

    public TokenRange withEnd(JavaToken end) {
        return new TokenRange(begin, assertNotNull(end));
    }
}
