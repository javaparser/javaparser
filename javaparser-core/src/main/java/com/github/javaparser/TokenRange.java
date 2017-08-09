package com.github.javaparser;

import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * The range of tokens covered by this node.
 */
public class TokenRange {
    public static final TokenRange INVALID = new TokenRange(JavaToken.INVALID, JavaToken.INVALID);

    private JavaToken begin;
    private JavaToken end;

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

    public void setBegin(JavaToken begin) {
        this.begin = begin;
    }

    public void setEnd(JavaToken end) {
        this.end = end;
    }

    public Range toRange() {
        return new Range(begin.getRange().begin, end.getRange().end);
    }

    public TokenRange withBegin(JavaToken begin) {
        return new TokenRange(assertNotNull(begin), end);
    }

    public TokenRange withEnd(JavaToken end) {
        return new TokenRange(begin, assertNotNull(end));
    }

    @Override
    public String toString() {
        JavaToken t = begin;
        StringBuilder result = new StringBuilder();
        while (true) {
            result.append(t.getText());
            if (t == end) {
                return result.toString();
            }
            Optional<JavaToken> next = t.getNextToken();
            if (next.isPresent()) {
                t = next.get();
            } else {
                return result.toString();
            }
        }
    }
}
