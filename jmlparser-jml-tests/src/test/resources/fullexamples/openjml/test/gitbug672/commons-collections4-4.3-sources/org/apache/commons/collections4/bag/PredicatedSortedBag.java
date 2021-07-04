/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.apache.commons.collections4.bag;

import java.util.Comparator;

import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.SortedBag;

/**
 * Decorates another {@link SortedBag} to validate that additions
 * match a specified predicate.
 * <p>
 * This bag exists to provide validation for the decorated bag.
 * It is normally created to decorate an empty bag.
 * If an object cannot be added to the bag, an {@link IllegalArgumentException} is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the bag.
 * <pre>
 * SortedBag bag = PredicatedSortedBag.predicatedSortedBag(new TreeBag(), NotNullPredicate.INSTANCE);
 * </pre>
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0
 */
public class PredicatedSortedBag<E> extends PredicatedBag<E> implements SortedBag<E> {

    /** Serialization version */
    private static final long serialVersionUID = 3448581314086406616L;

    /**
     * Factory method to create a predicated (validating) bag.
     * <p>
     * If there are any elements already in the bag being decorated, they
     * are validated.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated SortedBag
     * @throws NullPointerException if bag or predicate is null
     * @throws IllegalArgumentException if the bag contains invalid elements
     * @since 4.0
     */
    public static <E> PredicatedSortedBag<E> predicatedSortedBag(final SortedBag<E> bag,
                                                                 final Predicate<? super E> predicate) {
        return new PredicatedSortedBag<>(bag, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>If there are any elements already in the bag being decorated, they
     * are validated.
     *
     * @param bag  the bag to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if bag or predicate is null
     * @throws IllegalArgumentException if the bag contains invalid elements
     */
    protected PredicatedSortedBag(final SortedBag<E> bag, final Predicate<? super E> predicate) {
        super(bag, predicate);
    }

    /**
     * Gets the decorated sorted bag.
     *
     * @return the decorated bag
     */
    @Override
    protected SortedBag<E> decorated() {
        return (SortedBag<E>) super.decorated();
    }

    //-----------------------------------------------------------------------

    @Override
    public E first() {
        return decorated().first();
    }

    @Override
    public E last() {
        return decorated().last();
    }

    @Override
    public Comparator<? super E> comparator() {
        return decorated().comparator();
    }

}
