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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.Collection;
import java.util.Comparator;
import java.util.SortedMap;
import java.util.TreeMap;

import org.apache.commons.collections4.SortedBag;

/**
 * Implements {@link SortedBag}, using a {@link TreeMap} to provide the data storage.
 * This is the standard implementation of a sorted bag.
 * <p>
 * Order will be maintained among the bag members and can be viewed through the iterator.
 * <p>
 * A {@link org.apache.commons.collections4.Bag Bag} stores each object in the collection
 * together with a count of occurrences. Extra methods on the interface allow multiple
 * copies of an object to be added or removed at once. It is important to read the interface
 * javadoc carefully as several methods violate the {@link Collection} interface specification.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0 (previously in main package v2.0)
 */
public class TreeBag<E> extends AbstractMapBag<E> implements SortedBag<E>, Serializable {

    /** Serial version lock */
    private static final long serialVersionUID = -7740146511091606676L;

    /**
     * Constructs an empty {@link TreeBag}.
     */
    public TreeBag() {
        super(new TreeMap<E, MutableInteger>());
    }

    /**
     * Constructs an empty bag that maintains order on its unique representative
     * members according to the given {@link Comparator}.
     *
     * @param comparator the comparator to use
     */
    public TreeBag(final Comparator<? super E> comparator) {
        super(new TreeMap<E, MutableInteger>(comparator));
    }

    /**
     * Constructs a {@link TreeBag} containing all the members of the
     * specified collection.
     *
     * @param coll the collection to copy into the bag
     */
    public TreeBag(final Collection<? extends E> coll) {
        this();
        addAll(coll);
    }

    //-----------------------------------------------------------------------
    /**
     * {@inheritDoc}
     *
     * @throws IllegalArgumentException if the object to be added does not implement
     * {@link Comparable} and the {@link TreeBag} is using natural ordering
     * @throws NullPointerException if the specified key is null and this bag uses
     * natural ordering, or its comparator does not permit null keys
     */
    @Override
    public boolean add(final E object) {
        if(comparator() == null && !(object instanceof Comparable)) {
            if (object == null) {
                throw new NullPointerException();
            }
            throw new IllegalArgumentException("Objects of type " + object.getClass() + " cannot be added to " +
                                               "a naturally ordered TreeBag as it does not implement Comparable");
        }
        return super.add(object);
    }

    //-----------------------------------------------------------------------

    @Override
    public E first() {
        return getMap().firstKey();
    }

    @Override
    public E last() {
        return getMap().lastKey();
    }

    @Override
    public Comparator<? super E> comparator() {
        return getMap().comparator();
    }

    @Override
    protected SortedMap<E, AbstractMapBag.MutableInteger> getMap() {
        return (SortedMap<E, AbstractMapBag.MutableInteger>) super.getMap();
    }

    //-----------------------------------------------------------------------
    /**
     * Write the bag out using a custom routine.
     *
     * @param out  the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        out.writeObject(comparator());
        super.doWriteObject(out);
    }

    /**
     * Read the bag in using a custom routine.
     *
     * @param in  the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     */
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        @SuppressWarnings("unchecked")  // This will fail at runtime if the stream is incorrect
        final Comparator<? super E> comp = (Comparator<? super E>) in.readObject();
        super.doReadObject(new TreeMap<E, MutableInteger>(comp), in);
    }

}
