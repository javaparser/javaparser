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
package org.apache.commons.collections4.set;

import java.util.Set;

import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.collection.PredicatedCollection;

/**
 * Decorates another <code>Set</code> to validate that all additions
 * match a specified predicate.
 * <p>
 * This set exists to provide validation for the decorated set.
 * It is normally created to decorate an empty set.
 * If an object cannot be added to the set, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the set.
 * <pre>Set set = PredicatedSet.decorate(new HashSet(), NotNullPredicate.INSTANCE);</pre>
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of the elements in this set
 * @since 3.0
 */
public class PredicatedSet<E> extends PredicatedCollection<E> implements Set<E> {

    /** Serialization version */
    private static final long serialVersionUID = -684521469108685117L;

    /**
     * Factory method to create a predicated (validating) set.
     * <p>
     * If there are any elements already in the set being decorated, they
     * are validated.
     *
     * @param <E> the element type
     * @param set  the set to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a decorated set
     * @throws NullPointerException if set or predicate is null
     * @throws IllegalArgumentException if the set contains invalid elements
     * @since 4.0
     */
    public static <E> PredicatedSet<E> predicatedSet(final Set<E> set, final Predicate<? super E> predicate) {
        return new PredicatedSet<>(set, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the set being decorated, they
     * are validated.
     *
     * @param set  the set to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if set or predicate is null
     * @throws IllegalArgumentException if the set contains invalid elements
     */
    protected PredicatedSet(final Set<E> set, final Predicate<? super E> predicate) {
        super(set, predicate);
    }

    /**
     * Gets the set being decorated.
     *
     * @return the decorated set
     */
    @Override
    protected Set<E> decorated() {
        return (Set<E>) super.decorated();
    }

    @Override
    public boolean equals(final Object object) {
        return object == this || decorated().equals(object);
    }

    @Override
    public int hashCode() {
        return decorated().hashCode();
    }

}
