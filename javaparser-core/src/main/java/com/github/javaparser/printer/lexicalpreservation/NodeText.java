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

    private int findChild(Node child, int from) {
        for (int i=from; i<elements.size(); i++) {
            TextElement element = elements.get(i);
            if (element instanceof ChildTextElement) {
                ChildTextElement childNodeTextElement = (ChildTextElement)element;
                if (childNodeTextElement.getChild() == child) {
                    return i;
                }
            }
        }
        throw new IllegalArgumentException();
    }

    private int findToken(int tokenKind, int from) {
        for (int i=from; i<elements.size(); i++) {
            TextElement element = elements.get(i);
            if (element instanceof TokenTextElement){
                TokenTextElement tokenTextElement = (TokenTextElement)element;
                if (tokenTextElement.getTokenKind() == tokenKind) {
                    return i;
                }
            }
        }
        throw new IllegalArgumentException();
    }

    /**
     * Remove all elements between the given token (inclusive) and the given child (exclusive).
     * @param tokenKind
     * @param child
     */
    void removeTextBetween(int tokenKind, Node child) {
        int startDeletion = findToken(tokenKind, 0);
        int endDeletion = findChild(child, startDeletion + 1);
        removeBetweenIndexes(startDeletion, endDeletion);
    }

    private void removeBetweenIndexes(int startDeletion, int endDeletion) {
        int i = endDeletion;
        while (i >= startDeletion) {
            elements.remove(i--);
        }
    }

    private final static int WHITESPACE = 1;

    void removeTextBetween(Node child, int tokenKind, boolean removeSpaceImmediatelyAfter) {
        int startDeletion = findChild(child, 0);
        int endDeletion = findToken(tokenKind, startDeletion + 1);
        if (removeSpaceImmediatelyAfter && (getTextElement(endDeletion + 1) instanceof TokenTextElement) && ((TokenTextElement) getTextElement(endDeletion + 1)).getTokenKind() == WHITESPACE) {
            endDeletion++;
        }
        removeBetweenIndexes(startDeletion, endDeletion);
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

    // Visible for testing
    List<TextElement> getElements() {
        return elements;
    }

    public void removeToken(int tokenKind) {
        for (TextElement e : elements) {
            if ((e instanceof TokenTextElement) && ((TokenTextElement)e).getTokenKind() == tokenKind) {
                elements.remove(e);
                return;
            }
        }
        throw new IllegalArgumentException();
    }

    public void removeFromToken(Separator separator, boolean includingPreceedingSpace) {
        for (int i=elements.size() -1; i>=0; i--) {
            if (elements.get(i).isToken(separator.getTokenKind())) {
                while (elements.size() > i) {
                    elements.remove(i);
                }
                if (includingPreceedingSpace && elements.get(i - 1).isToken(Separator.SPACE.getTokenKind())) {
                    elements.remove(i - 1);
                }
                return;
            }
        }
        throw new IllegalArgumentException();
    }

    public void replace(Node oldChild, Node newChild) {
        int index = findChild(oldChild, 0);
        elements.remove(index);
        elements.add(index, new ChildTextElement(lexicalPreservingPrinter, newChild));
    }
}
