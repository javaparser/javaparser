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
import com.github.javaparser.ast.Modifier;

/**
 * A separator. We need to add or remove these elements when modifying the AST to keep
 * the text parsable and a correct layout.
 */
enum Separator {
    COMMA(ASTParserConstants.COMMA, ","),
    SPACE(1, " "),
    SEMICOLON(ASTParserConstants.SEMICOLON, ";"),
    NEWLINE(1, "\n"),
    TAB(1, "    "),
    PUBLIC(ASTParserConstants.PUBLIC, "public"),
    PROTECTED(ASTParserConstants.PROTECTED, "protected"),
    STATIC(ASTParserConstants.STATIC, "static"),
    EQUAL(ASTParserConstants.ASSIGN, "="),
    DEFAULT(ASTParserConstants._DEFAULT, "default"),
    EXTENDS(ASTParserConstants.EXTENDS, "extends"),
    IMPLEMENTS(ASTParserConstants.IMPLEMENTS, "implements");

    private String text;
    private int tokenKind;

    Separator(int tokenKind, String text) {
        this.text = text;
        this.tokenKind = tokenKind;
    }

    public String getText() {
        return text;
    }

    public int getTokenKind() {
        return tokenKind;
    }

    public static Separator fromModifier(Modifier modifier) {
        Separator separator = Separator.valueOf(modifier.name());
        if (separator == null) {
            throw new IllegalArgumentException(modifier.toString());
        }
        return separator;
    }
}
