/*
 * Copyright (C) 2013-2024 The JavaParser Team.
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

import java.util.NoSuchElementException;

public interface LookaheadIterator<E> {

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
    public E peek();

    /**
     * Returns the next element in iteration without advancing the underlying iterator.
     * If the iterator is already exhausted, null will be returned.
     *
     * @return the next element from the iterator
     * @throws NoSuchElementException if the iterator is already exhausted according to {@link #hasNext()}
     */
    public E element();

}
