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

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.comments.Comment;

/**
 * Represent the position of a child node in the NodeText of its parent.
 */
class ChildTextElement extends TextElement {
    private LexicalPreservingPrinter lexicalPreservingPrinter;
    private Node child;

    ChildTextElement(LexicalPreservingPrinter lexicalPreservingPrinter, Node child) {
        this.lexicalPreservingPrinter = lexicalPreservingPrinter;
        this.child = child;
    }

    String expand() {
        return lexicalPreservingPrinter.print(child);
    }

    Node getChild() {
        return child;
    }

    @Override
    boolean isToken(int tokenKind) {
        return false;
    }

    @Override
    boolean isNode(Node node) {
        return node == child;
    }

    NodeText getNodeTextForWrappedNode() {
        return lexicalPreservingPrinter.getOrCreateNodeText(child);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        ChildTextElement that = (ChildTextElement) o;

        if (!lexicalPreservingPrinter.equals(that.lexicalPreservingPrinter)) return false;
        return child.equals(that.child);

    }

    @Override
    public int hashCode() {
        int result = lexicalPreservingPrinter.hashCode();
        result = 31 * result + child.hashCode();
        return result;
    }

    @Override
    public String toString() {
        return "ChildTextElement{" + child + '}';
    }

    @Override
    public boolean isWhiteSpace() {
        return false;
    }

    @Override
    public boolean isSpaceOrTab() {
        return false;
    }

    @Override
    public boolean isNewline() {
        return false;
    }

    @Override
    public boolean isComment() {
        return child instanceof Comment;
    }

}
