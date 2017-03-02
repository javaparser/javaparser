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

package com.github.javaparser.printer.lexicalpreservation;

import com.github.javaparser.ASTParserConstants;
import com.github.javaparser.JavaToken;
import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.TokenConstants;
import com.github.javaparser.utils.Utils;

class TokenTextElement extends TextElement {

    private int tokenKind;
    private String text;

    public static TokenTextElement newLine() {
        return new TokenTextElement(TokenConstants.NEWLINE_TOKEN, Utils.EOL);
    }

    TokenTextElement(JavaToken token) {
        this(token.getKind(), token.getText());
    }

    TokenTextElement(int tokenKind, String text) {
        this.tokenKind = tokenKind;
        this.text = text;
    }

    TokenTextElement(int tokenKind) {
        String content = ASTParserConstants.tokenImage[tokenKind];
        if (content.startsWith("\"")) {
            content = content.substring(1, content.length() - 1);
        }
        if (tokenKind == TokenConstants.NEWLINE_TOKEN) {
            content = Utils.EOL;
        } else if (tokenKind == TokenConstants.SPACE_TOKEN) {
            content = " ";
        }
        this.tokenKind = tokenKind;
        this.text = content;
    }

    @Override
    String expand() {
        return text;
    }

    // Visible for testing
    String getText() {
        return text;
    }

    public int getTokenKind() {
        return tokenKind;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        TokenTextElement that = (TokenTextElement) o;

        if (tokenKind != that.tokenKind) return false;
        return text.equals(that.text);

    }

    @Override
    public int hashCode() {
        int result = tokenKind;
        result = 31 * result + text.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "TokenTextElement(" + tokenKind +
                ") {" + text + '}';
    }

    @Override
    boolean isToken(int tokenKind) {
        return this.tokenKind == tokenKind;
    }

    @Override
    boolean isNode(Node node) {
        return false;
    }

    @Override
    public boolean isWhiteSpace() {
        return TokenConstants.isWhitespace(tokenKind);
    }

    @Override
    public boolean isSpaceOrTab() {
        return TokenConstants.isSpaceOrTab(tokenKind);
    }

    boolean isWhiteSpaceOrComment() {
        return TokenConstants.isWhitespaceOrComment(tokenKind);
    }

    @Override
    public boolean isNewline() {
        return tokenKind == TokenConstants.NEWLINE_TOKEN;
    }
}
