package com.github.javaparser;

import java.util.Iterator;
import java.util.Optional;

import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * The range of tokens covered by this node.
 */
public class TokenRange implements Iterable<JavaToken> {
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

    public Optional<Range> toRange() {
        if (begin.getRange().isPresent() && end.getRange().isPresent()) {
            return Optional.of(new Range(begin.getRange().get().begin, end.getRange().get().end));
        }
        return Optional.empty();
    }

    public TokenRange withBegin(JavaToken begin) {
        return new TokenRange(assertNotNull(begin), end);
    }

    public TokenRange withEnd(JavaToken end) {
        return new TokenRange(begin, assertNotNull(end));
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder();
        for(JavaToken t: this) {
            result.append(t.getText());
        }
        return result.toString();
    }

    @Override
    public Iterator<JavaToken> iterator() {
        return new Iterator<JavaToken>() {
            private boolean hasNext = true;
            private JavaToken current = begin;

            @Override
            public boolean hasNext() {
                return hasNext;
            }

            @Override
            public JavaToken next() {
                JavaToken retval = current;
                if(current == null){
                    throw new IllegalStateException("Attempting to move past end of range.");
                }
                if (current == end) {
                    hasNext = false;
                }
                current = current.getNextToken().orElse(null);
                if(current == null && hasNext){
                    throw new IllegalStateException("End token is not linked to begin token.");
                }
                return retval;
            }
        };
    }
}
