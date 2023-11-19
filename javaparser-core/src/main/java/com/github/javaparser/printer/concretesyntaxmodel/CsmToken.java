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
package com.github.javaparser.printer.concretesyntaxmodel;

import static com.github.javaparser.TokenTypes.isEndOfLineToken;
import static com.github.javaparser.TokenTypes.isWhitespaceButNotEndOfLine;
import com.github.javaparser.GeneratedJavaParserConstants;
import com.github.javaparser.TokenTypes;
import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.lexicalpreservation.TextElement;
import com.github.javaparser.printer.lexicalpreservation.TokenTextElement;
import com.github.javaparser.utils.LineSeparator;

public class CsmToken implements CsmElement {

    private final int tokenType;

    private String content;

    public int getTokenType() {
        return tokenType;
    }

    public String getContent() {
        return content;
    }

    public CsmToken(int tokenType) {
        this.tokenType = tokenType;
        this.content = GeneratedJavaParserConstants.tokenImage[tokenType];
        if (content.startsWith("\"")) {
            content = content.substring(1, content.length() - 1);
        }
        // Replace "raw" values with escaped textual counterparts (e.g. newlines {@code \r\n})
        // and "placeholder" values ({@code <SPACE>}) with their textual counterparts
        if (isEndOfLineToken(tokenType)) {
            // Use the unescaped version
            content = LineSeparator.lookupEscaped(this.content).get().asRawString();
        } else if (isWhitespaceButNotEndOfLine(tokenType)) {
            content = " ";
        }
    }

    public CsmToken(int tokenType, String content) {
        this.tokenType = tokenType;
        this.content = content;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        if (isEndOfLineToken(tokenType)) {
            printer.println();
        } else {
            printer.print(getContent());
        }
    }

    @Override
    public String toString() {
        return String.format("%s(property:%s)", this.getClass().getSimpleName(), content);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;
        CsmToken csmToken = (CsmToken) o;
        if (tokenType != csmToken.tokenType)
            return false;
        if (content != null ? !content.equals(csmToken.content) : csmToken.content != null)
            return false;
        return true;
    }

    @Override
    public int hashCode() {
        int result = tokenType;
        result = 31 * result + (content != null ? content.hashCode() : 0);
        return result;
    }

    public boolean isWhiteSpace() {
        return TokenTypes.isWhitespace(tokenType);
    }

    public boolean isWhiteSpaceNotEol() {
        return isWhiteSpace() && !isNewLine();
    }

    public boolean isNewLine() {
        return TokenTypes.isEndOfLineToken(tokenType);
    }

    /*
     * Verifies if the content of the {@code CsmElement} is the same as the provided {@code TextElement}
     */
    @Override
    public boolean isCorrespondingElement(TextElement textElement) {
        return (textElement instanceof TokenTextElement) && ((TokenTextElement) textElement).getTokenKind() == getTokenType() && ((TokenTextElement) textElement).getText().equals(getContent());
    }
}
