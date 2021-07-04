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

import org.apache.commons.collections4.Transformer;
import org.apache.commons.collections4.collection.TransformedCollection;

/**
 * Decorates another <code>Set</code> to transform objects that are added.
 * <p>
 * The add methods are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of the elements in this set
 * @since 3.0
 */
public class TransformedSet<E> extends TransformedCollection<E> implements Set<E> {

    /** Serialization version */
    private static final long serialVersionUID = 306127383500410386L;

    /**
     * Factory method to create a transforming set.
     * <p>
     * If there are any elements already in the set being decorated, they
     * are NOT transformed.
     * Contrast this with {@link #transformedSet(Set, Transformer)}.
     *
     * @param <E> the element type
     * @param set  the set to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed set
     * @throws NullPointerException if set or transformer is null
     * @since 4.0
     */
    public static <E> TransformedSet<E> transformingSet(final Set<E> set,
            final Transformer<? super E, ? extends E> transformer) {
        return new TransformedSet<>(set, transformer);
    }

    /**
     * Factory method to create a transforming set that will transform
     * existing contents of the specified set.
     * <p>
     * If there are any elements already in the set being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingSet(Set, Transformer)}.
     *
     * @param <E> the element type
     * @param set  the set to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed set
     * @throws NullPointerException if set or transformer is null
     * @since 4.0
     */
    public static <E> Set<E> transformedSet(final Set<E> set, final Transformer<? super E, ? extends E> transformer) {
        final TransformedSet<E> decorated = new TransformedSet<>(set, transformer);
        if (set.size() > 0) {
            @SuppressWarnings("unchecked") // set is type E
            final E[] values = (E[]) set.toArray(); // NOPMD - false positive for generics
            set.clear();
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
     * If there are any elements already in the set being decorated, they
     * are NOT transformed.
     *
     * @param set  the set to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @throws NullPointerException if set or transformer is null
     */
    protected TransformedSet(final Set<E> set, final Transformer<? super E, ? extends E> transformer) {
        super(set, transformer);
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
