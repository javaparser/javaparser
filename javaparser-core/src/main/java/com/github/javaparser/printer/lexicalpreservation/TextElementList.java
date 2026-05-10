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

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;

/**
 * Default mutable implementation of {@link TextElementSequence}.
 *
 * <p>This class wraps an existing {@code List<TextElement>} without copying it.
 * All mutations directly affect the underlying list.
 *
 * <p>The implementation provides optimized search operations and clear semantics
 * for index-based manipulations required by lexical preservation operations.
 *
 * @since 3.28.0
 */
public class TextElementList implements TextElementSequence {

    private final List<TextElement> elements;

    /**
     * Creates a wrapper around the given list.
     * The list is NOT copied, mutations affect the original.
     *
     * @param elements the list to wrap
     * @throws NullPointerException if elements is null
     */
    public TextElementList(List<TextElement> elements) {
        this.elements = Objects.requireNonNull(elements, "elements cannot be null");
    }

    /**
     * Creates a new TextElementList containing the given elements.
     *
     * @param elements varargs of elements
     * @return a new list
     */
    public static TextElementList of(TextElement... elements) {
        return new TextElementList(new ArrayList<>(Arrays.asList(elements)));
    }

    /**
     * Creates a new TextElementList wrapping the given list.
     *
     * <p><b>IMPORTANT:</b> This method wraps the list directly without copying.
     * Modifications to the TextElementList will affect the original list.
     * Use {@link #copyOf(List)} if you need an independent copy.
     *
     * <p>This method is useful for chaining operations:
     * <pre>{@code
     * List<TextElement> result = TextElementList.of(list.subList(0, 10))
     *     .takeWhile(TextElement::isSpaceOrTab);
     * }</pre>
     *
     * @param elements the list to wrap (not copied)
     * @return a new TextElementList wrapping the given list
     * @throws NullPointerException if elements is null
     */
    public static TextElementList of(List<TextElement> elements) {
        return new TextElementList(elements);
    }

    /**
     * Creates an empty mutable TextElementList.
     *
     * @return an empty list
     */
    public static TextElementList empty() {
        return new TextElementList(new ArrayList<>());
    }

    /**
     * Creates a new TextElementList with a copy of the given list.
     *
     * @param elements the list to copy
     * @return a new list with copied elements
     * @throws NullPointerException if elements is null
     */
    public static TextElementList copyOf(List<TextElement> elements) {
        return new TextElementList(new ArrayList<>(elements));
    }

    // === SEARCH BY PREDICATE ===
    @Override
    public int findFirst(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        for (int i = 0; i < elements.size(); i++) {
            if (predicate.test(elements.get(i))) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int findLast(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        for (int i = elements.size() - 1; i >= 0; i--) {
            if (predicate.test(elements.get(i))) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int findNext(int fromIndex, Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        if (!isValidIndex(fromIndex)) {
            return -1;
        }
        for (int i = fromIndex; i < elements.size(); i++) {
            if (predicate.test(elements.get(i))) {
                return i;
            }
        }
        return -1;
    }

    @Override
    public int findPrevious(int fromIndex, Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        if (fromIndex < 0 || fromIndex >= elements.size()) {
            return -1;
        }
        for (int i = fromIndex; i >= 0; i--) {
            if (predicate.test(elements.get(i))) {
                return i;
            }
        }
        return -1;
    }

    // === FILTERING ===
    @Override
    public List<TextElement> takeWhile(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        List<TextElement> result = new ArrayList<>();
        for (TextElement element : elements) {
            if (!predicate.test(element)) {
                break;
            }
            result.add(element);
        }
        return result;
    }

    @Override
    public List<TextElement> subList(int fromIndex, int toIndex) {
        return elements.subList(fromIndex, toIndex);
    }

    // === MUTATION ===
    @Override
    public void insert(int index, TextElement element) {
        Objects.requireNonNull(element, "element cannot be null");
        elements.add(index, element);
    }

    @Override
    public void insertAll(int index, List<TextElement> elementsToInsert) {
        Objects.requireNonNull(elementsToInsert, "elements cannot be null");
        elements.addAll(index, elementsToInsert);
    }

    @Override
    public void remove(int index) {
        elements.remove(index);
    }

    @Override
    public void removeRange(int fromIndex, int toIndex) {
        if (!isValidIndex(fromIndex) || !isValidIndex(toIndex) || fromIndex > toIndex) {
            throw new IndexOutOfBoundsException(
                    "Invalid range: [" + fromIndex + ", " + toIndex + "] for size " + elements.size());
        }
        // toIndex is inclusive, subList.clear() expects exclusive upper bound
        elements.subList(fromIndex, toIndex + 1).clear();
    }

    // === ACCESS ===
    @Override
    public TextElement get(int index) {
        return elements.get(index);
    }

    @Override
    public boolean isValidIndex(int index) {
        return index >= 0 && index < elements.size();
    }

    @Override
    public int size() {
        return elements.size();
    }

    @Override
    public boolean isEmpty() {
        return elements.isEmpty();
    }

    @Override
    public List<TextElement> toList() {
        return Collections.unmodifiableList(elements);
    }

    @Override
    public List<TextElement> toMutableList() {
        return elements;
    }

    // === MATCHING (TERMINAL OPERATIONS) ===
    @Override
    public boolean anyMatch(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        for (TextElement element : elements) {
            if (predicate.test(element)) {
                return true;
            }
        }
        return false;
    }

    @Override
    public boolean allMatch(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        for (TextElement element : elements) {
            if (!predicate.test(element)) {
                return false;
            }
        }
        return true;
    }

    @Override
    public boolean noneMatch(Predicate<TextElement> predicate) {
        Objects.requireNonNull(predicate, "predicate cannot be null");
        return !anyMatch(predicate);
    }

    // === ITERATION ===
    @Override
    public TextElementIterator iterator(int fromIndex) {
        return new TextElementIterator(elements, fromIndex);
    }

    @Override
    public String toString() {
        return "TextElementList{size=" + elements.size() + "}";
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) return true;
        if (!(obj instanceof TextElementList)) return false;
        TextElementList other = (TextElementList) obj;
        return elements.equals(other.elements);
    }

    @Override
    public int hashCode() {
        return elements.hashCode();
    }
}
