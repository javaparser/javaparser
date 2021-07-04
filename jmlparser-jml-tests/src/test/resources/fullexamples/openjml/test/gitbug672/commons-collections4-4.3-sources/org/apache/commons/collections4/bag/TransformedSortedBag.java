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
import org.apache.commons.collections4.Transformer;

/**
 * Decorates another {@link SortedBag} to transform objects that are added.
 * <p>
 * The add methods are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0
 */
public class TransformedSortedBag<E> extends TransformedBag<E> implements SortedBag<E> {

    /** Serialization version */
    private static final long serialVersionUID = -251737742649401930L;

    /**
     * Factory method to create a transforming sorted bag.
     * <p>
     * If there are any elements already in the bag being decorated, they
     * are NOT transformed. Contrast this with {@link #transformedSortedBag(SortedBag, Transformer)}.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed SortedBag
     * @throws NullPointerException if bag or transformer is null
     * @since 4.0
     */
    public static <E> TransformedSortedBag<E> transformingSortedBag(final SortedBag<E> bag,
            final Transformer<? super E, ? extends E> transformer) {
        return new TransformedSortedBag<>(bag, transformer);
    }

    /**
     * Factory method to create a transforming sorted bag that will transform
     * existing contents of the specified sorted bag.
     * <p>
     * If there are any elements already in the bag being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingSortedBag(SortedBag, Transformer)}.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed SortedBag
     * @throws NullPointerException if bag or transformer is null
     * @since 4.0
     */
    public static <E> TransformedSortedBag<E> transformedSortedBag(final SortedBag<E> bag,
            final Transformer<? super E, ? extends E> transformer) {

        final TransformedSortedBag<E>  decorated = new TransformedSortedBag<>(bag, transformer);
        if (bag.size() > 0) {
            @SuppressWarnings("unchecked") // bag is type E
            final E[] values = (E[]) bag.toArray(); // NOPMD - false positive for generics
            bag.clear();
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
     * If there are any elements already in the bag being decorated, they
     * are NOT transformed.
     *
     * @param bag  the bag to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @throws NullPointerException if bag or transformer is null
     */
    protected TransformedSortedBag(final SortedBag<E> bag, final Transformer<? super E, ? extends E> transformer) {
        super(bag, transformer);
    }

    /**
     * Gets the decorated bag.
     *
     * @return the decorated bag
     */
    protected SortedBag<E> getSortedBag() {
        return (SortedBag<E>) decorated();
    }

    //-----------------------------------------------------------------------

    @Override
    public E first() {
        return getSortedBag().first();
    }

    @Override
    public E last() {
        return getSortedBag().last();
    }

    @Override
    public Comparator<? super E> comparator() {
        return getSortedBag().comparator();
    }

}
