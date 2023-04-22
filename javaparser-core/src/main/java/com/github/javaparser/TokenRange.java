/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2023 The JavaParser Team.
 *
 * This file is part of JavaParser.
 *
 * JavaParser can be used either under the terms of
 * a) the GNU Lesser General Public License as published by
 *     the Free Software Foundation, either version 3 of the License, or
 *     (at your option) any later version.
 * b) the terms of the Apache License
 *
 * You should have received a copy of both licenses in LICENCE.LGPL and
 * LICENCE.APACHE. Please refer to those files for details.
 *
 * JavaParser is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 */
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
        if (begin.hasRange() && end.hasRange()) {
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
        for (JavaToken t : this) {
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
                if (current == null) {
                    throw new IllegalStateException("Attempting to move past end of range.");
                }
                if (current == end) {
                    hasNext = false;
                }
                current = current.getNextToken().orElse(null);
                if (current == null && hasNext) {
                    throw new IllegalStateException("End token is not linked to begin token.");
                }
                return retval;
            }
        };
    }
}
