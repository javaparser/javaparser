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
import com.github.javaparser.ast.NodeList;

import java.util.LinkedList;
import java.util.List;

/**
 * This contains the lexical information for a single node.
 * It is basically a list of tokens and children.
 */
class NodeText {
    private LexicalPreservingPrinter lexicalPreservingPrinter;
    private List<TextElement> elements;

    //
    // Constructors
    //

    NodeText(LexicalPreservingPrinter lexicalPreservingPrinter, List<TextElement> elements) {
        this.lexicalPreservingPrinter = lexicalPreservingPrinter;
        this.elements = elements;
    }

    /**
     * Initialize with an empty list of elements.
     */
    NodeText(LexicalPreservingPrinter lexicalPreservingPrinter) {
        this(lexicalPreservingPrinter, new LinkedList<>());
    }

    //
    // Adding and removing elements
    //

    /**
     * Add an element at the end.
     */
    void addElement(TextElement nodeTextElement) {
        this.elements.add(nodeTextElement);
    }

    /**
     * Add an element at the given position.
     */
    void addElement(int index, TextElement nodeTextElement) {
        this.elements.add(index, nodeTextElement);
    }

    void addChild(Node child) {
        addElement(new ChildTextElement(lexicalPreservingPrinter, child));
    }

    void removeElementForChild(Node child) {
        elements.removeIf(e -> e instanceof ChildTextElement && ((ChildTextElement)e).getChild() == child);
    }

    private void addToken(int tokenKind, String text) {
        elements.add(new TokenTextElement(tokenKind, text));
    }

    private void addToken(int index, int tokenKind, String text) {
        elements.add(index, new TokenTextElement(tokenKind, text));
    }

    void addList(NodeList<?> children, boolean separatorAfterLast, Separator... separators) {
        for (int i=0; i<children.size(); i++) {
            Node child = children.get(i);
            addElement(new ChildTextElement(lexicalPreservingPrinter, child));
            if ((i+1)<children.size() || separatorAfterLast) {
                for (Separator s : separators) {
                    addToken(s);
                }
            }
        }
    }

    void addToken(Separator separator) {
        addToken(separator.getTokenKind(), separator.getText());
    }

    void addToken(int index, Separator separator) {
        addToken(index, separator.getTokenKind(), separator.getText());
    }

    /**
     * Remove all elements between the given token (inclusive) and the given child (exclusive).
     * @param tokenKind
     * @param child
     */
    void removeTextBetween(int tokenKind, Node child) {
        int lastTokenFound = -1;
        for (int i=0; i<elements.size(); i++) {
            TextElement element = elements.get(i);
            if (element instanceof ChildTextElement) {
                ChildTextElement childNodeTextElement = (ChildTextElement)element;
                if (childNodeTextElement.getChild() == child) {
                    if (lastTokenFound == -1) {
                        throw new IllegalArgumentException();
                    }
                    while (i > lastTokenFound) {
                        elements.remove(--i);
                    }
                    return;
                }
            } else if (element instanceof TokenTextElement){
                TokenTextElement tokenTextElement = (TokenTextElement)element;
                if (tokenTextElement.getTokenKind() == tokenKind) {
                    lastTokenFound = i;
                }
            }
        }
    }

    void removeTextBetween(Node child, int tokenKind, boolean removeSpaceImmediatelyAfter) {
       // FIXME
       removeTextBetween(tokenKind, child);
    }

    //
    // Other methods
    //

    /**
     * Generate the corresponding string.
     */
    String expand() {
        StringBuffer sb = new StringBuffer();

        elements.forEach(e -> sb.append(e.expand()));
        return sb.toString();
    }

    // Visible for testing
    int numberOfElements() {
        return elements.size();
    }

    // Visible for testing
    TextElement getTextElement(int index) {
        return elements.get(index);
    }
}
