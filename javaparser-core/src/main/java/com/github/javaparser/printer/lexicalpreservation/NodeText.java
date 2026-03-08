/*
 * Copyright (C) 2007-2010 Júlio Vilmar Gesser.
 * Copyright (C) 2011, 2013-2026 The JavaParser Team.
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
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * This contains the lexical information for a single node.
 * It is basically a list of tokens and children.
 *
 * <p>This class has been refactored to use {@link TextElementList} internally
 * for better code reuse and maintainability, while preserving the exact same
 * external API and behavior.
 */
class NodeText {

    // Changed from List<TextElement> to TextElementList for internal optimization
    private final TextElementList elements;

    public static final int NOT_FOUND = -1;

    //
    // Constructors
    //
    /**
     * Creates a NodeText wrapping the given list of elements.
     *
     * @param elements the list to wrap (will be wrapped in TextElementList)
     */
    NodeText(List<TextElement> elements) {
        this.elements = new TextElementList(elements);
    }

    /**
     * Initialize with an empty list of elements.
     */
    NodeText() {
        this(new LinkedList<>());
    }

    //
    // Adding elements
    //
    /**
     * Add an element at the end.
     */
    void addElement(TextElement nodeTextElement) {
        elements.insert(elements.size(), nodeTextElement);
    }

    /**
     * Add an element at the given position.
     */
    void addElement(int index, TextElement nodeTextElement) {
        elements.insert(index, nodeTextElement);
    }

    void addChild(Node child) {
        addElement(new ChildTextElement(child));
    }

    void addChild(int index, Node child) {
        addElement(index, new ChildTextElement(child));
    }

    void addToken(int tokenKind, String text) {
        addElement(new TokenTextElement(tokenKind, text));
    }

    void addToken(int index, int tokenKind, String text) {
        addElement(index, new TokenTextElement(tokenKind, text));
    }

    //
    // Finding elements
    //
    /**
     * Finds the first element matching the given matcher.
     *
     * @param matcher the matcher to use
     * @return the index of the first matching element
     * @throws IllegalArgumentException if no matching element is found
     */
    int findElement(TextElementMatcher matcher) {
        return findElement(matcher, 0);
    }

    /**
     * Finds the first element matching the given matcher, starting from the given index.
     *
     * @param matcher the matcher to use
     * @param from the starting index (inclusive)
     * @return the index of the first matching element
     * @throws IllegalArgumentException if no matching element is found
     */
    int findElement(TextElementMatcher matcher, int from) {
        int res = tryToFindElement(matcher, from);
        if (res == NOT_FOUND) {
            throw new IllegalArgumentException(String.format(
                    "I could not find child '%s' from position %d. Elements: %s", matcher, from, elements.toList()));
        }
        return res;
    }

    /**
     * Tries to find an element matching the given matcher, starting from the given index.
     * Returns NOT_FOUND if no matching element is found.
     *
     * @param matcher the matcher to use
     * @param from the starting index (inclusive)
     * @return the index of the first matching element, or NOT_FOUND
     */
    int tryToFindElement(TextElementMatcher matcher, int from) {
        return elements.findNext(from, matcher::match);
    }

    /**
     * Finds the first occurrence of the given child node.
     *
     * @param child the child to find
     * @return the index of the child
     * @throws IllegalArgumentException if child is not found
     */
    int findChild(Node child) {
        return findChild(child, 0);
    }

    /**
     * Finds the first occurrence of the given child node, starting from the given index.
     *
     * @param child the child to find
     * @param from the starting index (inclusive)
     * @return the index of the child
     * @throws IllegalArgumentException if child is not found
     */
    int findChild(Node child, int from) {
        return findElement(TextElementMatchers.byNode(child), from);
    }

    /**
     * Tries to find the first occurrence of the given child node.
     *
     * @param child the child to find
     * @return the index of the child, or NOT_FOUND
     */
    int tryToFindChild(Node child) {
        return tryToFindChild(child, 0);
    }

    /**
     * Tries to find the first occurrence of the given child node, starting from the given index.
     *
     * @param child the child to find
     * @param from the starting index (inclusive)
     * @return the index of the child, or NOT_FOUND
     */
    int tryToFindChild(Node child, int from) {
        return tryToFindElement(TextElementMatchers.byNode(child), from);
    }

    //
    // Removing single elements
    //
    /**
     * Removes the first element matching the given matcher.
     * Optionally removes following whitespace.
     *
     * @param matcher the matcher to use
     * @param potentiallyFollowingWhitespace if true, removes following whitespace element
     * @throws IllegalArgumentException if no matching element is found
     * @throws UnsupportedOperationException if whitespace removal is requested but no element follows
     */
    public void remove(TextElementMatcher matcher, boolean potentiallyFollowingWhitespace) {
        // Find the matching element using our optimized search
        int index = tryToFindElement(matcher, 0);
        if (index == NOT_FOUND) {
            throw new IllegalArgumentException("No matching element found");
        }
        // Remove the element
        elements.remove(index);
        // Optionally remove following whitespace
        if (potentiallyFollowingWhitespace) {
            if (index < elements.size()) {
                if (elements.get(index).isWhiteSpace()) {
                    elements.remove(index);
                }
            } else {
                throw new UnsupportedOperationException("There is no element to remove!");
            }
        }
    }

    //
    // Removing sequences
    //
    /**
     * Removes the element at the given index.
     *
     * @param index the index of the element to remove
     */
    void removeElement(int index) {
        elements.remove(index);
    }

    //
    // Replacing elements
    //
    /**
     * Replaces the element at the position matched by the given matcher
     * with the given new element.
     *
     * @param position the matcher to find the element to replace
     * @param newElement the new element
     * @throws IllegalArgumentException if no matching element is found
     */
    void replace(TextElementMatcher position, TextElement newElement) {
        int index = findElement(position, 0);
        elements.remove(index);
        elements.insert(index, newElement);
    }

    /**
     * Replaces the element at the position matched by the given matcher
     * with the given collection of new elements.
     *
     * @param position the matcher to find the element to replace
     * @param newElements the new elements
     * @throws IllegalArgumentException if no matching element is found
     */
    void replace(TextElementMatcher position, Collection<? extends TextElement> newElements) {
        int index = findElement(position, 0);
        elements.remove(index);
        elements.insertAll(index, (List<TextElement>) newElements);
    }

    //
    // Other methods
    //
    /**
     * Generate the corresponding string by expanding all elements.
     *
     * @return the expanded string representation
     */
    String expand() {
        StringBuilder sb = new StringBuilder();
        // Use the underlying list's forEach for efficiency
        elements.toList().forEach(e -> sb.append(e.expand()));
        return sb.toString();
    }

    /**
     * Returns the number of elements.
     * Visible for testing.
     *
     * @return the number of elements
     */
    int numberOfElements() {
        return elements.size();
    }

    /**
     * Returns the element at the given index.
     * Visible for testing.
     *
     * @param index the index
     * @return the element at that index
     */
    TextElement getTextElement(int index) {
        return elements.get(index);
    }

    /**
     * Returns the underlying list of elements.
     * Visible for testing.
     *
     * <p><b>IMPORTANT:</b> This returns the internal mutable list.
     * External modifications will affect this NodeText.
     *
     * @return the list of elements (mutable)
     */
    List<TextElement> getElements() {
        return elements.toMutableList();
    }

    @Override
    public String toString() {
        return "NodeText{" + elements.toList() + '}';
    }
}
