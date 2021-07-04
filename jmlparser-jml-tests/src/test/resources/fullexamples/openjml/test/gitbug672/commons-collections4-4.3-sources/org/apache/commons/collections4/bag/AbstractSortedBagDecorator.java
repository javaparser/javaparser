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

import org.apache.commons.collections4.SortedBag;

/**
 * Decorates another <code>SortedBag</code> to provide additional behaviour.
 * <p>
 * Methods are forwarded directly to the decorated bag.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0
 */
public abstract class AbstractSortedBagDecorator<E>
        extends AbstractBagDecorator<E> implements SortedBag<E> {

    /** Serialization version */
    private static final long serialVersionUID = -8223473624050467718L;

    /**
     * Constructor only used in deserialization, do not use otherwise.
     * @since 3.1
     */
    protected AbstractSortedBagDecorator() {
        super();
    }

    /**
     * Constructor that wraps (not copies).
     *
     * @param bag  the bag to decorate, must not be null
     * @throws NullPointerException if bag is null
     */
    protected AbstractSortedBagDecorator(final SortedBag<E> bag) {
        super(bag);
    }

    /**
     * Gets the bag being decorated.
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
