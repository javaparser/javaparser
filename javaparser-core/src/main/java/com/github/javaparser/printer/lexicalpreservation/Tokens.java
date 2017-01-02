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

public class Tokens {

    public static TokenTextElement comma() {
        return new TokenTextElement(ASTParserConstants.COMMA, ",");
    }

    public static TokenTextElement semicolon() {
        return new TokenTextElement(ASTParserConstants.SEMICOLON, ";");
    }

    public static TokenTextElement space() {
        return new TokenTextElement(1, " ");
    }

    public static TokenTextElement tab() {
        return new TokenTextElement(1, "    ");
    }

    public static TokenTextElement newline() {
        return new TokenTextElement(3, "\n");
    }

    public static TokenTextElement equal() {
        return new TokenTextElement(ASTParserConstants.ASSIGN, "=");
    }

    public static TokenTextElement create(int tokenKind) {
        String text = ASTParserConstants.tokenImage[tokenKind];
        if (text.startsWith("\"") && text.endsWith("\"")) {
            text = text.substring(1, text.length() - 1);
        }
        return new TokenTextElement(tokenKind, text);
    }

    public static TokenTextElement fromModifier(Modifier modifier) {
        try {
            int tokenKind = (int)ASTParserConstants.class.getField(modifier.name()).get(null);
            String text = modifier.name().toLowerCase();
            return new TokenTextElement(tokenKind, text);
        } catch (IllegalAccessException|NoSuchFieldException e) {
            throw new IllegalArgumentException("Unable to handle " + modifier, e);
        }
    }
}
