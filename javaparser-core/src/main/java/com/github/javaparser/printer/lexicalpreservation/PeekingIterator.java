/*
 * Copyright (C) 2011, 2013-2024 The JavaParser Team.
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
import java.util.NoSuchElementException;
import java.util.Objects;

/**
 * Decorates an iterator to support one-element lookahead while iterating.
 * <p>
 * The decorator supports the removal operation, but an {@link IllegalStateException}
 * will be thrown if {@link #remove()}, {@link #add()}, {@link #set()}} is called directly after a call to
 * {@link #peek()} or {@link #element()}.
 *
 * @param <E> the type of elements returned by this iterator.
 * @since 4.0
 */
public class PeekingIterator<E> implements ListIterator<E>, LookaheadIterator<E> {

    /** The iterator being decorated. */
    private final ListIterator<E> iterator;

    /** Indicates that the decorated iterator is exhausted. */
    private boolean exhausted;

    /** Indicates if the lookahead slot is filled. */
    private boolean slotFilled;

    /** The current slot for lookahead. */
    private E slot;

    /**
     * Decorates the specified iterator to support one-element lookahead.
     * <p>
     * If the iterator is already a {@link PeekingIterator} it is returned directly.
     *
     * @param <E>  the element type
     * @param iterator  the iterator to decorate
     * @return a new peeking iterator
     * @throws NullPointerException if the iterator is null
     */
    public <E> PeekingIterator<E> peekingIterator(final ListIterator<E> iterator) {
        Objects.requireNonNull(iterator, "iterator");
        if (iterator instanceof PeekingIterator<?>) {
            final PeekingIterator<E> it = (PeekingIterator<E>) iterator;
            return it;
        }
        return new PeekingIterator<>(iterator);
    }


    /**
     * Constructor.
     *
     * @param iterator  the iterator to decorate
     */
    public PeekingIterator(final ListIterator<E> iterator) {
        this.iterator = iterator;
    }

    /**
     * Constructor.
     *
     * @param list  the provider of the iterator to decorate
     */
    public PeekingIterator(final List<E> list) {
        this.iterator = list.listIterator();
    }

    private void fill() {
        if (exhausted || slotFilled) {
            return;
        }
        if (iterator.hasNext()) {
            slot = iterator.next();
            slotFilled = true;
        } else {
            exhausted = true;
            slot = null;
            slotFilled = false;
        }
    }

    @Override
    public boolean hasNext() {
        if (exhausted) {
            return false;
        }
        return slotFilled || iterator.hasNext();
    }

    /**
     * Returns the next element in iteration without advancing the underlying iterator.
     * If the iterator is already exhausted, null will be returned.
     * <p>
     * Note: this method does not throw a {@link NoSuchElementException} if the iterator
     * is already exhausted. If you want such a behavior, use {@link #element()} instead.
     * <p>
     * The rationale behind this is to follow the {@link java.util.Queue} interface
     * which uses the same terminology.
     *
     * @return the next element from the iterator
     */
    @Override
	public E peek() {
        fill();
        return exhausted ? null : slot;
    }

    /**
     * Returns the next element in iteration without advancing the underlying iterator.
     * If the iterator is already exhausted, null will be returned.
     *
     * @return the next element from the iterator
     * @throws NoSuchElementException if the iterator is already exhausted according to {@link #hasNext()}
     */
    @Override
	public E element() {
        fill();
        if (exhausted) {
            throw new NoSuchElementException();
        }
        return slot;
    }

    @Override
    public E next() {
        if (!hasNext()) {
            throw new NoSuchElementException();
        }
        final E x = slotFilled ? slot : iterator.next();
        // reset the lookahead slot
        slot = null;
        slotFilled = false;
        return x;
    }

    /**
     * {@inheritDoc}
     *
     * @throws IllegalStateException if {@link #peek()} or {@link #element()} has been called
     *   prior to the call to {@link #remove()}
     */
    @Override
    public void remove() {
        if (slotFilled) {
            throw new IllegalStateException("peek() or element() called before remove()");
        }
        iterator.remove();
    }


	@Override
	public boolean hasPrevious() {
		return iterator.hasPrevious();
	}


	@Override
	public E previous() {
		return iterator.previous();
	}


	@Override
	public int nextIndex() {
		return iterator.nextIndex();
	}

	/*
	 * Returns the index of the element that would be returned by the last call to next.
	 * Returns list size - 1 if the listiterator is at the end of the list.
	 * Returns -1 if the listiterator is at the beginning of the list.
	 */
	public int currentIndex() {
		if (!hasPrevious()) return previousIndex();
		return nextIndex() - 1;
	}


	@Override
	public int previousIndex() {
		return iterator.previousIndex();
	}


	@Override
	public void set(E e) {
		if (slotFilled) {
            throw new IllegalStateException("peek() or element() called before set()");
        }
		iterator.set(e);
	}


	@Override
	public void add(E e) {
		if (slotFilled) {
            throw new IllegalStateException("peek() or element() called before add()");
        }
		iterator.add(e);
	}

}
