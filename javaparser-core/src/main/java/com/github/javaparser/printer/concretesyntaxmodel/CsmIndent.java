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

import com.github.javaparser.ast.Node;
import com.github.javaparser.printer.SourcePrinter;
import com.github.javaparser.printer.lexicalpreservation.TextElement;
import com.github.javaparser.printer.lexicalpreservation.TokenTextElement;

public class CsmIndent implements CsmElement {

    @Override
    public void prettyPrint(Node node, SourcePrinter printer) {
        printer.indent();
    }

    /*
     * Verifies if the content of the {@code CsmElement} is the same as the provided {@code TextElement}
     */
    @Override
    public boolean isCorrespondingElement(TextElement textElement) {
        return (textElement instanceof TokenTextElement) && ((TokenTextElement) textElement).isSpaceOrTab();
    }

    @Override
    public int hashCode() {
        return 1;
    }

    @Override
    public boolean equals(Object obj) {
        return obj instanceof CsmIndent;
    }
}
