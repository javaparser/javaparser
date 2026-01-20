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

import java.util.List;
import java.util.Objects;
import java.util.function.Predicate;
import java.util.stream.Stream;

/**
 * Contract for a specialized sequence of TextElements with enhanced search
 * and modification capabilities for lexical preservation operations.
 *
 * <p>Unlike standard {@link List}, this interface provides:
 * <ul>
 *   <li>Index-based search with predicates (findFirst, findLast, findNext, findPrevious)</li>
 *   <li>Element-based search (indexOf, lastIndexOf with overloads)</li>
 *   <li>Controlled mutations (insert, remove) where caller manages index adjustments</li>
 * </ul>
 *
 * <p><b>Thread safety:</b> Implementations are not required to be thread-safe.
 *
 * <p><b>Index management:</b> Mutation operations modify the underlying list directly.
 * Callers are responsible for tracking index changes after mutations.
 *
 * @since 3.28.0
 */
public interface TextElementSequence {

    // === SEARCH BY PREDICATE ===

    /**
     * Finds the first index where the predicate matches, searching forward from index 0.
     *
     * @param predicate the condition to test
     * @return the first matching index, or -1 if no match found
     * @throws NullPointerException if predicate is null
     */
    int findFirst(Predicate<TextElement> predicate);

    /**
     * Finds the last index where the predicate matches, searching backward from the end.
     *
     * @param predicate the condition to test
     * @return the last matching index, or -1 if no match found
     * @throws NullPointerException if predicate is null
     */
    int findLast(Predicate<TextElement> predicate);

    /**
     * Finds the next index where the predicate matches, searching forward from fromIndex (inclusive).
     *
     * @param fromIndex the starting index (inclusive)
     * @param predicate the condition to test
     * @return the next matching index, or -1 if no match found
     * @throws NullPointerException if predicate is null
     */
    int findNext(int fromIndex, Predicate<TextElement> predicate);

    /**
     * Finds the previous index where the predicate matches, searching backward from fromIndex (inclusive).
     *
     * @param fromIndex the starting index (inclusive)
     * @param predicate the condition to test
     * @return the previous matching index, or -1 if no match found
     * @throws NullPointerException if predicate is null
     */
    int findPrevious(int fromIndex, Predicate<TextElement> predicate);

    // === MATCHING (TERMINAL OPERATIONS) ===

    /**
     * Tests whether any element in this sequence matches the given predicate.
     *
     * <p>This is a short-circuiting terminal operation: it stops as soon as
     * a matching element is found and returns true immediately.
     *
     * <p>Examples:
     * <pre>{@code
     * // Check if list contains any comment
     * boolean hasComment = list.anyMatch(TextElement::isComment);
     *
     * // Check if list contains any token with specific text
     * boolean hasIdentifier = list.anyMatch(el ->
     *     el instanceof TokenTextElement &&
     *     ((TokenTextElement) el).getText().equals("myVar")
     * );
     * }</pre>
     *
     * @param predicate the predicate to test elements against
     * @return true if any element matches the predicate, false otherwise
     *         (returns false for empty sequences)
     * @throws NullPointerException if predicate is null
     */
    boolean anyMatch(Predicate<TextElement> predicate);

    /**
     * Tests whether all elements in this sequence match the given predicate.
     *
     * <p>This is a short-circuiting terminal operation: it stops as soon as
     * a non-matching element is found and returns false immediately.
     *
     * <p>Returns true for empty sequences (vacuous truth).
     *
     * <p>Examples:
     * <pre>{@code
     * // Check if all elements are whitespace
     * boolean allWhitespace = list.allMatch(TextElement::isSpaceOrTab);
     *
     * // Check if all elements are comments
     * boolean allComments = list.allMatch(TextElement::isComment);
     * }</pre>
     *
     * @param predicate the predicate to test elements against
     * @return true if all elements match the predicate (or sequence is empty),
     *         false otherwise
     * @throws NullPointerException if predicate is null
     */
    boolean allMatch(Predicate<TextElement> predicate);

    /**
     * Tests whether no elements in this sequence match the given predicate.
     *
     * <p>This is a short-circuiting terminal operation: it stops as soon as
     * a matching element is found and returns false immediately.
     *
     * <p>Returns true for empty sequences.
     *
     * <p>Equivalent to {@code !anyMatch(predicate)}.
     *
     * <p>Examples:
     * <pre>{@code
     * // Check if list has no comments
     * boolean noComments = list.noneMatch(TextElement::isComment);
     *
     * // Check if list has no newlines
     * boolean noNewlines = list.noneMatch(TextElement::isNewline);
     * }</pre>
     *
     * @param predicate the predicate to test elements against
     * @return true if no elements match the predicate (or sequence is empty),
     *         false otherwise
     * @throws NullPointerException if predicate is null
     */
    boolean noneMatch(Predicate<TextElement> predicate);

    // === SEARCH BY ELEMENT ===

    /**
     * Finds the first occurrence of the specified element.
     * Equivalent to {@code findFirst(e -> Objects.equals(e, element))}.
     *
     * @param element the element to search for (may be null)
     * @return the first occurrence index, or -1 if not found
     */
    default int indexOf(TextElement element) {
        return findFirst(e -> Objects.equals(e, element));
    }

    /**
     * Finds the last occurrence of the specified element.
     * Equivalent to {@code findLast(e -> Objects.equals(e, element))}.
     *
     * @param element the element to search for (may be null)
     * @return the last occurrence index, or -1 if not found
     */
    default int lastIndexOf(TextElement element) {
        return findLast(e -> Objects.equals(e, element));
    }

    /**
     * Finds the next occurrence of element starting from fromIndex (inclusive).
     * Equivalent to {@code findNext(fromIndex, e -> Objects.equals(e, element))}.
     *
     * @param fromIndex the starting index (inclusive)
     * @param element the element to search for (may be null)
     * @return the next occurrence index, or -1 if not found
     */
    default int indexOf(int fromIndex, TextElement element) {
        return findNext(fromIndex, e -> Objects.equals(e, element));
    }

    /**
     * Finds the previous occurrence of element before fromIndex (inclusive).
     * Equivalent to {@code findPrevious(fromIndex, e -> Objects.equals(e, element))}.
     *
     * @param fromIndex the starting index (inclusive)
     * @param element the element to search for (may be null)
     * @return the previous occurrence index, or -1 if not found
     */
    default int lastIndexOf(int fromIndex, TextElement element) {
        return findPrevious(fromIndex, e -> Objects.equals(e, element));
    }

    // === FILTERING ===

    /**
     * Returns a new list containing elements from the start until the predicate fails.
     * The returned list is independent of this sequence.
     *
     * @param predicate the condition to test
     * @return a new list of matching elements
     * @throws NullPointerException if predicate is null
     */
    List<TextElement> takeWhile(Predicate<TextElement> predicate);

    /**
     * Returns a sublist view [fromIndex, toIndex).
     * The returned list is backed by this sequence, so changes affect both.
     *
     * @param fromIndex low endpoint (inclusive)
     * @param toIndex high endpoint (exclusive)
     * @return a sublist view
     * @throws IndexOutOfBoundsException if indices are out of range
     */
    List<TextElement> subList(int fromIndex, int toIndex);

    // === MUTATION ===

    /**
     * Inserts element at the specified index.
     * <b>WARNING:</b> Caller must adjust subsequent indices manually.
     *
     * @param index position to insert at
     * @param element element to insert
     * @throws IndexOutOfBoundsException if index is out of range
     * @throws NullPointerException if element is null
     */
    void insert(int index, TextElement element);

    /**
     * Inserts all elements at the specified index.
     * <b>WARNING:</b> Caller must adjust subsequent indices manually.
     *
     * @param index position to insert at
     * @param elements elements to insert
     * @throws IndexOutOfBoundsException if index is out of range
     * @throws NullPointerException if elements is null
     */
    void insertAll(int index, List<TextElement> elements);

    /**
     * Removes the element at the specified index.
     * <b>WARNING:</b> Caller must adjust subsequent indices manually.
     *
     * @param index position to remove from
     * @throws IndexOutOfBoundsException if index is out of range
     */
    void remove(int index);

    /**
     * Removes elements in range [fromIndex, toIndex] (inclusive on both ends).
     * <b>WARNING:</b> Caller must adjust subsequent indices manually.
     *
     * @param fromIndex start of range (inclusive)
     * @param toIndex end of range (inclusive)
     * @throws IndexOutOfBoundsException if indices are out of range or fromIndex > toIndex
     */
    void removeRange(int fromIndex, int toIndex);

    // === ACCESS ===

    /**
     * Returns the element at the specified index.
     *
     * @param index the index
     * @return the element at that position
     * @throws IndexOutOfBoundsException if index is out of range
     */
    TextElement get(int index);

    /**
     * Checks if the index is valid (0 <= index < size).
     *
     * @param index the index to check
     * @return true if index is valid
     */
    boolean isValidIndex(int index);

    /**
     * Returns the number of elements in this sequence.
     *
     * @return the size
     */
    int size();

    /**
     * Checks if this sequence is empty.
     *
     * @return true if size is 0
     */
    boolean isEmpty();

    /**
     * Returns an unmodifiable view of the underlying list.
     * Changes to the original list are visible in the returned view.
     *
     * @return an unmodifiable list view
     */
    List<TextElement> toList();

    /**
     * Returns the underlying mutable list.
     *
     * <p><b>WARNING:</b> This exposes the internal list directly.
     * Modifications will affect this sequence.
     *
     * @return the mutable list
     */
    List<TextElement> toMutableList();

    // === ITERATION ===

    /**
     * Returns an iterator starting at the specified index.
     *
     * @param fromIndex the starting position
     * @return an iterator with position tracking
     * @throws IndexOutOfBoundsException if fromIndex is out of range
     */
    TextElementIterator iterator(int fromIndex);

    /**
     * Returns an iterator starting at index 0.
     *
     * @return an iterator from the beginning
     */
    default TextElementIterator iterator() {
        return iterator(0);
    }

    /**
     * Returns a stream of elements for functional operations.
     *
     * @return a stream over the elements
     */
    default Stream<TextElement> stream() {
        return toList().stream();
    }
}
