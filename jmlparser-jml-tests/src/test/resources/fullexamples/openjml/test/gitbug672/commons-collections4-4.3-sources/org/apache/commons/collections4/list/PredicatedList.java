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
package org.apache.commons.collections4.list;

import java.util.Collection;
import java.util.List;
import java.util.ListIterator;

import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.collection.PredicatedCollection;
import org.apache.commons.collections4.iterators.AbstractListIteratorDecorator;

/**
 * Decorates another <code>List</code> to validate that all additions
 * match a specified predicate.
 * <p>
 * This list exists to provide validation for the decorated list.
 * It is normally created to decorate an empty list.
 * If an object cannot be added to the list, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the list.
 * <pre>
 * {@code
 * List<String> list =
 *   PredicatedList.predicatedList(new ArrayList<String>(), PredicateUtils.notNullPredicate());
 * }
 * </pre>
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @since 3.0
 */
public class PredicatedList<E> extends PredicatedCollection<E> implements List<E> {

    /** Serialization version */
    private static final long serialVersionUID = -5722039223898659102L;

    /**
     * Factory method to create a predicated (validating) list.
     * <p>
     * If there are any elements already in the list being decorated, they
     * are validated.
     *
     * @param <T> the type of the elements in the list
     * @param list  the list to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated list
     * @throws NullPointerException if list or predicate is null
     * @throws IllegalArgumentException if the list contains invalid elements
     * @since 4.0
     */
    public static <T> PredicatedList<T> predicatedList(final List<T> list, final Predicate<? super T> predicate) {
        return new PredicatedList<>(list, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the list being decorated, they
     * are validated.
     *
     * @param list  the list to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if list or predicate is null
     * @throws IllegalArgumentException if the list contains invalid elements
     */
    protected PredicatedList(final List<E> list, final Predicate<? super E> predicate) {
        super(list, predicate);
    }

    /**
     * Gets the list being decorated.
     *
     * @return the decorated list
     */
    @Override
    protected List<E> decorated() {
        return (List<E>) super.decorated();
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
    public E get(final int index) {
        return decorated().get(index);
    }

    @Override
    public int indexOf(final Object object) {
        return decorated().indexOf(object);
    }

    @Override
    public int lastIndexOf(final Object object) {
        return decorated().lastIndexOf(object);
    }

    @Override
    public E remove(final int index) {
        return decorated().remove(index);
    }

    //-----------------------------------------------------------------------

    @Override
    public void add(final int index, final E object) {
        validate(object);
        decorated().add(index, object);
    }

    @Override
    public boolean addAll(final int index, final Collection<? extends E> coll) {
        for (final E aColl : coll) {
            validate(aColl);
        }
        return decorated().addAll(index, coll);
    }

    @Override
    public ListIterator<E> listIterator() {
        return listIterator(0);
    }

    @Override
    public ListIterator<E> listIterator(final int i) {
        return new PredicatedListIterator(decorated().listIterator(i));
    }

    @Override
    public E set(final int index, final E object) {
        validate(object);
        return decorated().set(index, object);
    }

    @Override
    public List<E> subList(final int fromIndex, final int toIndex) {
        final List<E> sub = decorated().subList(fromIndex, toIndex);
        return new PredicatedList<>(sub, predicate);
    }

    /**
     * Inner class Iterator for the PredicatedList
     */
    protected class PredicatedListIterator extends AbstractListIteratorDecorator<E> {

        /**
         * Create a new predicated list iterator.
         *
         * @param iterator  the list iterator to decorate
         */
        protected PredicatedListIterator(final ListIterator<E> iterator) {
            super(iterator);
        }

        @Override
        public void add(final E object) {
            validate(object);
            getListIterator().add(object);
        }

        @Override
        public void set(final E object) {
            validate(object);
            getListIterator().set(object);
        }
    }

}
