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
package com.github.javaparser.printer.lexicalpreservation;

import java.util.Optional;
import com.github.javaparser.JavaToken;
import com.github.javaparser.JavaToken.Kind;
import com.github.javaparser.Range;
import com.github.javaparser.ast.Node;

public class TokenTextElement extends TextElement {

    private final JavaToken token;

    TokenTextElement(JavaToken token) {
        this.token = token;
    }

    TokenTextElement(int tokenKind, String text) {
        this(new JavaToken(tokenKind, text));
    }

    TokenTextElement(int tokenKind) {
        this(new JavaToken(tokenKind));
    }

    @Override
    public String expand() {
        return token.getText();
    }

    // Visible for testing
    public String getText() {
        return token.getText();
    }

    public int getTokenKind() {
        return token.getKind();
    }

    public JavaToken getToken() {
        return token;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        TokenTextElement that = (TokenTextElement) o;
        return token.equals(that.token);
    }

    @Override
    public int hashCode() {
        return token.hashCode();
    }

    @Override
    public String toString() {
        return token.toString();
    }

    @Override
    boolean isToken(int tokenKind) {
        return token.getKind() == tokenKind;
    }

    @Override
    boolean isNode(Node node) {
        return false;
    }

    @Override
    public boolean isWhiteSpace() {
        return token.getCategory().isWhitespace();
    }

    @Override
    public boolean isSpaceOrTab() {
        return token.getCategory().isWhitespaceButNotEndOfLine();
    }

    @Override
    public boolean isComment() {
        return token.getCategory().isComment();
    }

    @Override
    public boolean isSeparator() {
        return token.getCategory().isSeparator();
    }

    @Override
    public boolean isNewline() {
        return token.getCategory().isEndOfLine();
    }

    @Override
    public boolean isChildOfClass(Class<? extends Node> nodeClass) {
        return false;
    }

    @Override
    public boolean isIdentifier() {
        return getToken().getCategory().isIdentifier();
    }

    @Override
    public boolean isKeyword() {
        return getToken().getCategory().isKeyword();
    }

    @Override
    public boolean isLiteral() {
        return getToken().getCategory().isLiteral();
    }

    @Override
    public boolean isPrimitive() {
        return Kind.valueOf(getTokenKind()).isPrimitive();
    }

    @Override
    Optional<Range> getRange() {
        return token.getRange();
    }

    @Override
    public void accept(LexicalPreservingVisitor visitor) {
        visitor.visit(this);
    }
}
