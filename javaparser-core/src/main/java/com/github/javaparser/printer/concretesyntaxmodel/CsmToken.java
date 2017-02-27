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

package com.github.javaparser.printer.concretesyntaxmodel;

import com.github.javaparser.GeneratedModuleInfoParserConstants;
import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.utils.Utils;


public class CsmToken implements CsmElement {
    private int tokenType;
    private String content;
    private TokenContentCalculator tokenContentCalculator;

    public static int NEWLINE_TOKEN = 3;
    public static int SPACE_TOKEN = 1;
    public static int SPACE_TOKEN_ALT = 32;
    public static int TAB_TOKEN = 31;
    public static int EOF_TOKEN = 0;

    public interface TokenContentCalculator {
        String calculate(Node node);
    }

    public int getTokenType() {
        return tokenType;
    }

    public String getContent(Node node) {
        if (tokenContentCalculator != null) {
            return tokenContentCalculator.calculate(node);
        }
        return content;
    }

    public CsmToken(int tokenType) {
        this.tokenType = tokenType;
        this.content = GeneratedModuleInfoParserConstants.tokenImage[tokenType];
        if (content.startsWith("\"")) {
            content = content.substring(1, content.length() - 1);
        }
        if (tokenType == NEWLINE_TOKEN) {
            content = Utils.EOL;
        } else if (tokenType == SPACE_TOKEN) {
            content = " ";
        }
    }

    public CsmToken(int tokenType, String content) {
        this.tokenType = tokenType;
        this.content = content;
    }

    public CsmToken(int tokenType, TokenContentCalculator tokenContentCalculator) {
        this.tokenType = tokenType;
        this.tokenContentCalculator = tokenContentCalculator;
    }

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        if (tokenType == 3) {
            printer.println();
        } else {
            printer.print(getContent(node));
        }
    }

    @Override
    public String toString() {
        return "token(" + content + ")";
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        CsmToken csmToken = (CsmToken) o;

        if (tokenType != csmToken.tokenType) return false;
        if (content != null ? !content.equals(csmToken.content) : csmToken.content != null) return false;
        return tokenContentCalculator != null ? tokenContentCalculator.equals(csmToken.tokenContentCalculator) : csmToken.tokenContentCalculator == null;
    }

    @Override
    public int hashCode() {
        int result = tokenType;
        result = 31 * result + (content != null ? content.hashCode() : 0);
        result = 31 * result + (tokenContentCalculator != null ? tokenContentCalculator.hashCode() : 0);
        return result;
    }

    public boolean isWhiteSpace() {
        return tokenType == NEWLINE_TOKEN || tokenType == SPACE_TOKEN || tokenType == EOF_TOKEN || tokenType == TAB_TOKEN || tokenType == SPACE_TOKEN_ALT;
    }
}
