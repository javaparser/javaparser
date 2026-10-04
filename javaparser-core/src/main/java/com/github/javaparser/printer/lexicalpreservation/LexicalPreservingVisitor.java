/*
 * Copyright (C) 2013-2026 The JavaParser Team.
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

import static com.github.javaparser.GeneratedJavaParserConstants.MINUS;
import static com.github.javaparser.GeneratedJavaParserConstants.PLUS;

import java.io.StringWriter;

public class LexicalPreservingVisitor {

    private StringWriter writer;

    private TokenTextElement previous;

    public LexicalPreservingVisitor() {
        this(new StringWriter());
    }

    public LexicalPreservingVisitor(StringWriter writer) {
        this.writer = writer;
    }

    public void visit(ChildTextElement child) {
        child.accept(this);
    }

    public void visit(TokenTextElement token) {
        String text = token.getText();
        if (previous != null
                && ((previous.isToken(PLUS) && text.startsWith("+"))
                        || (previous.isToken(MINUS) && text.startsWith("-")))) {
            // Preserve token boundaries introduced by AST edits, not individual characters.
            writer.append(' ');
        }
        writer.append(text);
        if (!text.isEmpty()) {
            previous = token;
        }
    }

    @Override
    public String toString() {
        return writer.toString();
    }
}
