/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2016 The JavaParser Team.
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

import java.util.List;
import java.util.Optional;

import static com.github.javaparser.Position.*;
import static com.github.javaparser.utils.Utils.assertNotNull;

/**
 * A token from a parsed source file.
 * (Awkwardly named "Java"Token since JavaCC already generates an internal class Token.)
 */
public class JavaToken {
    public static final JavaToken INVALID = new JavaToken();

    private final Range range;
    private int kind;
    private final String text;
    private final Optional<JavaToken> previousToken;
    private Optional<JavaToken> nextToken = Optional.empty();

    private JavaToken() {
        range = new Range(pos(-1,-1), pos(-1,-1));
        kind = 0;
        text = "INVALID";
        previousToken = Optional.empty();
    }

    public JavaToken(Token token, List<JavaToken> tokens) {
        Range range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.endColumn);
        String text = token.image;

        // You could be puzzled by the following lines
        //
        // The reason why these lines are necessary is the fact that Java is ambiguous. There are cases where the
        // sequence of characters ">>>" and ">>" should be recognized as the single tokens ">>>" and ">>". In other
        // cases however we want to split those characters in single GT tokens (">").
        //
        // For example, in expressions ">>" and ">>>" are valid, while when defining types we could have this:
        //
        //   List<List<Set<String>>>>
        //
        // You can see that the sequence ">>>>" should be interpreted as four consecutive ">" tokens closing a type
        // parameter list.
        //
        // The JavaCC handle this case by first recognizing always the longest token, and then depending on the context
        // putting back the unused chars in the stream. However in those cases the token provided is invalid: it has an
        // image corresponding to the text originally recognized, without considering that after some characters could
        // have been put back into the stream.
        //
        // So in the case of:
        //
        //   List<List<Set<String>>>>
        //                       ___   -> recognized as ">>>", then ">>" put back in the stream but
        //                                Token(type=GT, image=">>>") passed to this class
        //                        ___  -> recognized as ">>>", then ">>" put back in the stream but
        //                                Token(type=GT, image=">>>") passed to this class
        //                         __  -> recognized as ">>", then ">" put back in the stream but
        //                                Token(type=GT, image=">>") passed to this class
        //                          _  -> Token(type=GT, image=">") good!
        //
        // So given the image could be wrong but the type is correct, we look at the type of the token and we fix
        // the image. Everybody is happy and we can keep this horrible thing as our little secret.

        if (token.kind == GeneratedJavaParserConstants.GT) {
            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn);
            text = ">";
        } else if (token.kind == GeneratedJavaParserConstants.RSIGNEDSHIFT) {
            range = Range.range(token.beginLine, token.beginColumn, token.endLine, token.beginColumn + 1);
            text = ">>";
        }
        this.range = range;
        this.kind = token.kind;
        this.text = text;
        if (!tokens.isEmpty()) {
            final JavaToken previousToken = tokens.get(tokens.size() - 1);
            this.previousToken = Optional.of(previousToken);
            previousToken.nextToken = Optional.of(this);
        } else {
            previousToken = Optional.empty();
        }
    }

    public JavaToken(Range range, int kind, String text, Optional<JavaToken> previousToken, Optional<JavaToken> nextToken) {
        this.range = range;
        this.kind = kind;
        this.text = text;
        this.previousToken = previousToken;
        this.nextToken = nextToken;
    }

    public Range getRange() {
        return range;
    }

    public int getKind() {
        return kind;
    }

    void setKind(int kind) {
        this.kind = kind;
    }

    public String getText() {
        return text;
    }

    public Optional<JavaToken> getNextToken() {
        return nextToken;
    }

    public Optional<JavaToken> getPreviousToken() {
        return previousToken;
    }

    @Override
    public String toString() {
        return text;
    }

    /**
     * Check if the position is usable. Does not know what it is pointing at, so it can't check if the position is after
     * the end of the source.
     */
    public boolean valid() {
        return !invalid();
    }

    public boolean invalid() {
        return this == INVALID;
    }

    public JavaToken orIfInvalid(JavaToken anotherToken) {
        assertNotNull(anotherToken);
        if (valid() || anotherToken.invalid()) {
            return this;
        }
        return anotherToken;
    }


}
