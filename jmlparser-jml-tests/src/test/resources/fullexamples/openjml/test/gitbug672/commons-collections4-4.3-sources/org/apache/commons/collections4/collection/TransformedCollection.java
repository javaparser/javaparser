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
package org.apache.commons.collections4.collection;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.commons.collections4.Transformer;

/**
 * Decorates another {@link Collection} to transform objects that are added.
 * <p>
 * The add methods are affected by this class.
 * Thus objects must be removed or searched for using their transformed form.
 * For example, if the transformation converts Strings to Integers, you must
 * use the Integer form to remove objects.
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of the elements in the collection
 * @since 3.0
 */
public class TransformedCollection<E> extends AbstractCollectionDecorator<E> {

    /** Serialization version */
    private static final long serialVersionUID = 8692300188161871514L;

    /** The transformer to use */
    protected final Transformer<? super E, ? extends E> transformer;

    /**
     * Factory method to create a transforming collection.
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are NOT transformed.
     * Contrast this with {@link #transformedCollection(Collection, Transformer)}.
     *
     * @param <E> the type of the elements in the collection
     * @param coll  the collection to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed collection
     * @throws NullPointerException if collection or transformer is null
     * @since 4.0
     */
    public static <E> TransformedCollection<E> transformingCollection(final Collection<E> coll,
            final Transformer<? super E, ? extends E> transformer) {
        return new TransformedCollection<>(coll, transformer);
    }

    /**
     * Factory method to create a transforming collection that will transform
     * existing contents of the specified collection.
     * <p>
     * If there are any elements already in the collection being decorated, they
     * will be transformed by this method.
     * Contrast this with {@link #transformingCollection(Collection, Transformer)}.
     *
     * @param <E> the type of the elements in the collection
     * @param collection  the collection to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @return a new transformed Collection
     * @throws NullPointerException if collection or transformer is null
     * @since 4.0
     */
    public static <E> TransformedCollection<E> transformedCollection(final Collection<E> collection,
            final Transformer<? super E, ? extends E> transformer) {

        final TransformedCollection<E> decorated = new TransformedCollection<>(collection, transformer);
        // null collection & transformer are disallowed by the constructor call above
        if (collection.size() > 0) {
            @SuppressWarnings("unchecked") // collection is of type E
            final E[] values = (E[]) collection.toArray(); // NOPMD - false positive for generics
            collection.clear();
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
     * If there are any elements already in the collection being decorated, they
     * are NOT transformed.
     *
     * @param coll  the collection to decorate, must not be null
     * @param transformer  the transformer to use for conversion, must not be null
     * @throws NullPointerException if collection or transformer is null
     */
    protected TransformedCollection(final Collection<E> coll, final Transformer<? super E, ? extends E> transformer) {
        super(coll);
        if (transformer == null) {
            throw new NullPointerException("Transformer must not be null");
        }
        this.transformer = transformer;
    }

    /**
     * Transforms an object.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param object  the object to transform
     * @return a transformed object
     */
    protected E transform(final E object) {
        return transformer.transform(object);
    }

    /**
     * Transforms a collection.
     * <p>
     * The transformer itself may throw an exception if necessary.
     *
     * @param coll  the collection to transform
     * @return a transformed object
     */
    protected Collection<E> transform(final Collection<? extends E> coll) {
        final List<E> list = new ArrayList<>(coll.size());
        for (final E item : coll) {
            list.add(transform(item));
        }
        return list;
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean add(final E object) {
        return decorated().add(transform(object));
    }

    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        return decorated().addAll(transform(coll));
    }

}
