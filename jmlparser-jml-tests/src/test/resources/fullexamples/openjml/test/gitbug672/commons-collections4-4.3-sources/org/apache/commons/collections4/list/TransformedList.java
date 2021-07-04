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

import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.collection.TransformedCollection;
import org.apache.commons.collections4.iterators.AbstractListIteratorDecorator;

/**
 * Decorates another <code>List</code> to transform objects that are added.
 * <p>
 * The add and set methods are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @since 3.0
 */
public class TransformedList<E> extends TransformedCollection<E> implements List<E> {

    /** Serialization version */
    private static final long serialVersionUID = 1077193035000013141L;

    /**
     * Factory method to create a transforming list.
     * <p>
     * If there are any elements already in the list being decorated, they
     * are NOT transformed.
     * Contrast this with {@link #transformedList(List, Transformer)}.
     *
     * @param <E> the type of the elements in the list
     * @param list  the list to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed list
     * @throws NullPointerException if list or transformer is null
     * @since 4.0
     */
    public static <E> TransformedList<E> transformingList(final List<E> list,
                                                          final Transformer<? super E, ? extends E> transformer) {
        return new TransformedList<>(list, transformer);
    }

    /**
     * Factory method to create a transforming list that will transform
     * existing contents of the specified list.
     * <p>
     * If there are any elements already in the list being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingList(List, Transformer)}.
     *
     * @param <E> the type of the elements in the list
     * @param list  the list to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed List
     * @throws NullPointerException if list or transformer is null
     * @since 4.0
     */
    public static <E> TransformedList<E> transformedList(final List<E> list,
                                                         final Transformer<? super E, ? extends E> transformer) {
        final TransformedList<E> decorated = new TransformedList<>(list, transformer);
        if (list.size() > 0) {
            @SuppressWarnings("unchecked") // list is of type E
            final E[] values = (E[]) list.toArray(); // NOPMD - false positive for generics
            list.clear();
            for (final E value : values) {
                decorated.decorated().add(transformer.transform(value));
            }
        }
        return decorated;
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the list being decorated, they
     * are NOT transformed.
     *
     * @param list  the list to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @throws NullPointerException if list or transformer is null
     */
    protected TransformedList(final List<E> list, final Transformer<? super E, ? extends E> transformer) {
        super(list, transformer);
    }

    /**
     * Gets the decorated list.
     *
     * @return the decorated list
     */
    protected List<E> getList() {
        return (List<E>) decorated();
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
        return getList().get(index);
    }

    @Override
    public int indexOf(final Object object) {
        return getList().indexOf(object);
    }

    @Override
    public int lastIndexOf(final Object object) {
        return getList().lastIndexOf(object);
    }

    @Override
    public E remove(final int index) {
        return getList().remove(index);
    }

    //-----------------------------------------------------------------------

    @Override
    public void add(final int index, E object) {
        object = transform(object);
        getList().add(index, object);
    }

    @Override
    public boolean addAll(final int index, Collection<? extends E> coll) {
        coll = transform(coll);
        return getList().addAll(index, coll);
    }

    @Override
    public ListIterator<E> listIterator() {
        return listIterator(0);
    }

    @Override
    public ListIterator<E> listIterator(final int i) {
        return new TransformedListIterator(getList().listIterator(i));
    }

    @Override
    public E set(final int index, E object) {
        object = transform(object);
        return getList().set(index, object);
    }

    @Override
    public List<E> subList(final int fromIndex, final int toIndex) {
        final List<E> sub = getList().subList(fromIndex, toIndex);
        return new TransformedList<>(sub, transformer);
    }

    /**
     * Inner class Iterator for the TransformedList
     */
    protected class TransformedListIterator extends AbstractListIteratorDecorator<E> {

        /**
         * Create a new transformed list iterator.
         *
         * @param iterator  the list iterator to decorate
         */
        protected TransformedListIterator(final ListIterator<E> iterator) {
            super(iterator);
        }

        @Override
        public void add(E object) {
            object = transform(object);
            getListIterator().add(object);
        }

        @Override
        public void set(E object) {
            object = transform(object);
            getListIterator().set(object);
        }
    }

}
