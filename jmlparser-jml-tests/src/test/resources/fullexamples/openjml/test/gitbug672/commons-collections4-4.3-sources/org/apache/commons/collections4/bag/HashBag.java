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
import java.util.HashMap;

/**
 * Implements {@code Bag}, using a {@link HashMap} to provide the
 * data storage. This is the standard implementation of a bag.
 * <p>
 * A {@code Bag} stores each object in the collection together with a
 * count of occurrences. Extra methods on the interface allow multiple copies
 * of an object to be added or removed at once. It is important to read the
 * interface javadoc carefully as several methods violate the
 * {@link Collection} interface specification.
 *
 * @param <E> the type of elements in this bag
 * @since 3.0 (previously in main package v2.0)
 */
public class HashBag<E> extends AbstractMapBag<E> implements Serializable {

    /** Serial version lock */
    private static final long serialVersionUID = -6561115435802554013L;

    /**
     * Constructs an empty {@link HashBag}.
     */
    public HashBag() {
        super(new HashMap<E, MutableInteger>());
    }

    /**
     * Constructs a bag containing all the members of the given collection.
     *
     * @param coll  a collection to copy into this bag
     */
    public HashBag(final Collection<? extends E> coll) {
        this();
        addAll(coll);
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
        super.doReadObject(new HashMap<E, MutableInteger>(), in);
    }

}
