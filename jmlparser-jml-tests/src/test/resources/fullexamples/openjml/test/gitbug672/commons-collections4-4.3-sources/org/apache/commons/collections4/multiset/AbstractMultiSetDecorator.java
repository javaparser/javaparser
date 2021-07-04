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
import org.apache.commons.collections4.collection.AbstractCollectionDecorator;

/**
 * Decorates another <code>MultSet</code> to provide additional behaviour.
 * <p>
 * Methods are forwarded directly to the decorated multiset.
 *
 * @param <E> the type held in the multiset
 * @since 4.1
 */
public abstract class AbstractMultiSetDecorator<E>
        extends AbstractCollectionDecorator<E> implements MultiSet<E> {

    /** Serialization version */
    private static final long serialVersionUID = 20150610L;

    /**
     * Constructor only used in deserialization, do not use otherwise.
     */
    protected AbstractMultiSetDecorator() {
        super();
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param multiset  the multiset to decorate, must not be null
     * @throws NullPointerException if multiset is null
     */
    protected AbstractMultiSetDecorator(final MultiSet<E> multiset) {
        super(multiset);
    }

    /**
     * Gets the multiset being decorated.
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
    public int getCount(final Object object) {
        return decorated().getCount(object);
    }

    @Override
    public int setCount(final E object, final int count) {
        return decorated().setCount(object, count);
    }

    @Override
    public int add(final E object, final int count) {
        return decorated().add(object, count);
    }

    @Override
    public int remove(final Object object, final int count) {
        return decorated().remove(object, count);
    }

    @Override
    public Set<E> uniqueSet() {
        return decorated().uniqueSet();
    }

    @Override
    public Set<Entry<E>> entrySet() {
        return decorated().entrySet();
    }

}
