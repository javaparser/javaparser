/*
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
import java.util.ListIterator;

/**
 * Iterator that tracks its current position in a TextElement list.
 *
 * <p>Unlike standard {@link ListIterator}, this class provides direct access
 * to the current index via {@link #currentIndex()}, which returns the index of
 * the element that was returned by the most recent call to {@link #next()} or
 * {@link #previous()}.
 *
 * <p>This iterator is a replacement for the internal {@code ArrayIterator} class,
 * with clearer semantics and better naming. It correctly handles bidirectional
 * iteration by maintaining the current index internally.
 *
 * @since 3.28.0
 */
public class TextElementIterator implements ListIterator<TextElement> {

    private final ListIterator<TextElement> delegate;

    private int currentIndex;

    /**
     * Creates an iterator starting at the specified index.
     * The current index is initialized to -1, indicating that no element
     * has been read yet.
     *
     * @param elements the list to iterate over
     * @param fromIndex the starting index (cursor position)
     * @throws IndexOutOfBoundsException if fromIndex is out of range
     */
    public TextElementIterator(List<TextElement> elements, int fromIndex) {
        this.delegate = elements.listIterator(fromIndex);
        // No element read yet
        this.currentIndex = -1;
    }

    /**
     * Returns the index of the element that was returned by the most recent call
     * to {@link #next()} or {@link #previous()}.
     *
     * <p>This method can be called multiple times without side effects - it will
     * always return the same value until the next call to {@link #next()},
     * {@link #previous()}, or {@link #remove()}.
     *
     * <p><b>Important:</b> If neither {@link #next()} nor {@link #previous()} has
     * been called yet, or if {@link #remove()} was called after the last call to
     * {@link #next()} or {@link #previous()}, this method returns -1.
     *
     * @return the index of the current element, or -1 if no element has been read
     *         or the current element was removed
     */
    public int currentIndex() {
        return currentIndex;
    }

    // === LISTITERATOR METHODS WITH INDEX TRACKING ===
    @Override
    public boolean hasNext() {
        return delegate.hasNext();
    }

    @Override
    public TextElement next() {
        TextElement result = delegate.next();
        // After next(), previousIndex() points to the element we just read
        currentIndex = delegate.previousIndex();
        return result;
    }

    @Override
    public boolean hasPrevious() {
        return delegate.hasPrevious();
    }

    @Override
    public TextElement previous() {
        TextElement result = delegate.previous();
        // After previous(), nextIndex() points to the element we just read
        currentIndex = delegate.nextIndex();
        return result;
    }

    @Override
    public int nextIndex() {
        return delegate.nextIndex();
    }

    @Override
    public int previousIndex() {
        return delegate.previousIndex();
    }

    @Override
    public void remove() {
        delegate.remove();
        // After remove, there is no current element
        currentIndex = -1;
    }

    @Override
    public void set(TextElement element) {
        delegate.set(element);
        // Current index doesn't change when replacing an element
    }

    @Override
    public void add(TextElement element) {
        delegate.add(element);
        // After add(), the added element becomes the current element
        currentIndex = delegate.previousIndex();
    }
}
