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
package org.apache.commons.collections4.multiset;

import java.util.Set;

import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.collection.PredicatedCollection;

/**
 * Decorates another {@link MultiSet} to validate that additions
 * match a specified predicate.
 * <p>
 * This multiset exists to provide validation for the decorated multiset.
 * It is normally created to decorate an empty multiset.
 * If an object cannot be added to the multiset, an {@link IllegalArgumentException}
 * is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the multiset.
 * <pre>
 * MultiSet&lt;E&gt; set =
 *      PredicatedMultiSet.predicatedMultiSet(new HashMultiSet&lt;E&gt;(),
 *                                            NotNullPredicate.notNullPredicate());
 * </pre>
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public class PredicatedMultiSet<E> extends PredicatedCollection<E> implements MultiSet<E> {

    /** Serialization version */
    private static final long serialVersionUID = 20150629L;

    /**
     * Factory method to create a predicated (validating) multiset.
     * <p>
     * If there are any elements already in the multiset being decorated, they
     * are validated.
     *
     * @param <E> the type of the elements in the multiset
     * @param multiset  the multiset to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated MultiSet
     * @throws NullPointerException if multiset or predicate is null
     * @throws IllegalArgumentException if the multiset contains invalid elements
     */
    public static <E> PredicatedMultiSet<E> predicatedMultiSet(final MultiSet<E> multiset,
                                                               final Predicate<? super E> predicate) {
        return new PredicatedMultiSet<>(multiset, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the multiset being decorated, they
     * are validated.
     *
     * @param multiset  the multiset to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if multiset or predicate is null
     * @throws IllegalArgumentException if the multiset contains invalid elements
     */
    protected PredicatedMultiSet(final MultiSet<E> multiset, final Predicate<? super E> predicate) {
        super(multiset, predicate);
    }

    /**
     * Gets the decorated multiset.
     *
     * @return the decorated multiset
     */
    @Override
    protected MultiSet<E> decorated() {
        return (MultiSet<E>) super.decorated();
    }

    @Override
    public boolean equals(final Object object) {
        return object == this || decorated().equals(object);
    }

    @Override
    public int hashCode() {
        return decorated().hashCode();
    }

    //-----------------------------------------------------------------------

    @Override
    public int add(final E object, final int count) {
        validate(object);
        return decorated().add(object, count);
    }

    @Override
    public int remove(final Object object, final int count) {
        return decorated().remove(object, count);
    }

    @Override
    public int getCount(final Object object) {
        return decorated().getCount(object);
    }

    @Override
    public int setCount(final E object, final int count) {
        validate(object);
        return decorated().setCount(object, count);
    }

    @Override
    public Set<E> uniqueSet() {
        return decorated().uniqueSet();
    }

    @Override
    public Set<MultiSet.Entry<E>> entrySet() {
        return decorated().entrySet();
    }

}
