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

import java.util.Set;

import org.apache.commons.collections4.Bag;
import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.collection.TransformedCollection;
import org.apache.commons.collections4.set.TransformedSet;

/**
 * Decorates another {@link Bag} to transform objects that are added.
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
public class TransformedBag<E> extends TransformedCollection<E> implements Bag<E> {

    /** Serialization version */
    private static final long serialVersionUID = 5421170911299074185L;

    /**
     * Factory method to create a transforming bag.
     * <p>
     * If there are any elements already in the bag being decorated, they
     * are NOT transformed. Contrast this with {@link #transformedBag(Bag, Transformer)}.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed Bag
     * @throws NullPointerException if bag or transformer is null
     * @since 4.0
     */
    public static <E> Bag<E> transformingBag(final Bag<E> bag, final Transformer<? super E, ? extends E> transformer) {
        return new TransformedBag<>(bag, transformer);
    }

    /**
     * Factory method to create a transforming bag that will transform
     * existing contents of the specified bag.
     * <p>
     * If there are any elements already in the bag being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingBag(Bag, Transformer)}.
     *
     * @param <E> the type of the elements in the bag
     * @param bag  the bag to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed Bag
     * @throws NullPointerException if bag or transformer is null
     * @since 4.0
     */
    public static <E> Bag<E> transformedBag(final Bag<E> bag, final Transformer<? super E, ? extends E> transformer) {
        final TransformedBag<E> decorated = new TransformedBag<>(bag, transformer);
        if (bag.size() > 0) {
            @SuppressWarnings("unchecked") // Bag is of type E
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
    protected TransformedBag(final Bag<E> bag, final Transformer<? super E, ? extends E> transformer) {
        super(bag, transformer);
    }

    /**
     * Gets the decorated bag.
     *
     * @return the decorated bag
     */
    protected Bag<E> getBag() {
        return (Bag<E>) decorated();
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
        return getBag().getCount(object);
    }

    @Override
    public boolean remove(final Object object, final int nCopies) {
        return getBag().remove(object, nCopies);
    }

    //-----------------------------------------------------------------------

    @Override
    public boolean add(final E object, final int nCopies) {
        return getBag().add(transform(object), nCopies);
    }

    @Override
    public Set<E> uniqueSet() {
        final Set<E> set = getBag().uniqueSet();
        return TransformedSet.<E>transformingSet(set, transformer);
    }

}
