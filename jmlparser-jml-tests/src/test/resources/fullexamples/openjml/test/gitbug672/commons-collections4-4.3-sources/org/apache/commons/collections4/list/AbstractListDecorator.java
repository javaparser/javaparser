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

import org.apache.commons.collections4.collection.AbstractCollectionDecorator;

/**
 * Decorates another {@link List} to provide additional behaviour.
 * <p>
 * Methods are forwarded directly to the decorated list.
 *
 * @param <E> the type of the elements in the list
 * @since 3.0
 */
public abstract class AbstractListDecorator<E> extends AbstractCollectionDecorator<E>
        implements List<E> {

    /** Serialization version--necessary in an abstract class? */
    private static final long serialVersionUID = 4500739654952315623L;

    /**
     * Constructor only used in deserialization, do not use otherwise.
     * @since 3.1
     */
    protected AbstractListDecorator() {
        super();
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param list  the list to decorate, must not be null
     * @throws NullPointerException if list is null
     */
    protected AbstractListDecorator(final List<E> list) {
        super(list);
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
    public void add(final int index, final E object) {
        decorated().add(index, object);
    }

    @Override
    public boolean addAll(final int index, final Collection<? extends E> coll) {
        return decorated().addAll(index, coll);
    }

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
    public ListIterator<E> listIterator() {
        return decorated().listIterator();
    }

    @Override
    public ListIterator<E> listIterator(final int index) {
        return decorated().listIterator(index);
    }

    @Override
    public E remove(final int index) {
        return decorated().remove(index);
    }

    @Override
    public E set(final int index, final E object) {
        return decorated().set(index, object);
    }

    @Override
    public List<E> subList(final int fromIndex, final int toIndex) {
        return decorated().subList(fromIndex, toIndex);
    }

}
