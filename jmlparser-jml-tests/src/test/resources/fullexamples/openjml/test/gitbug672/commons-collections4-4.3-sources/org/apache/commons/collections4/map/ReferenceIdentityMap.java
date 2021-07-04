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
package org.apache.commons.collections4.map;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.ref.Reference;

/**
 * A <code>Map</code> implementation that allows mappings to be
 * removed by the garbage collector and matches keys and values based
 * on <code>==</code> not <code>equals()</code>.
 * <p>
 * When you construct a <code>ReferenceIdentityMap</code>, you can specify what kind
 * of references are used to store the map's keys and values.
 * If non-hard references are used, then the garbage collector can remove
 * mappings if a key or value becomes unreachable, or if the JVM's memory is
 * running low. For information on how the different reference types behave,
 * see {@link Reference}.
 * </p>
 * <p>
 * Different types of references can be specified for keys and values.
 * The default constructor uses hard keys and soft values, providing a
 * memory-sensitive cache.
 * </p>
 * <p>
 * This map is similar to
 * {@link org.apache.commons.collections4.map.ReferenceMap ReferenceMap}.
 * It differs in that keys and values in this class are compared using <code>==</code>.
 * </p>
 * <p>
 * This map will violate the detail of various Map and map view contracts.
 * As a general rule, don't compare this map to other maps.
 * </p>
 * <p>
 * This {@link java.util.Map Map} implementation does <i>not</i> allow null elements.
 * Attempting to add a null key or value to the map will raise a <code>NullPointerException</code>.
 * </p>
 * <p>
 * This implementation is not synchronized.
 * You can use {@link java.util.Collections#synchronizedMap} to
 * provide synchronized access to a <code>ReferenceIdentityMap</code>.
 * Remember that synchronization will not stop the garbage collector removing entries.
 * </p>
 * <p>
 * All the available iterators can be reset back to the start by casting to
 * <code>ResettableIterator</code> and calling <code>reset()</code>.
 * </p>
 * <p>
 * <strong>Note that ReferenceIdentityMap is not synchronized and is not thread-safe.</strong>
 * If you wish to use this map from multiple threads concurrently, you must use
 * appropriate synchronization. The simplest approach is to wrap this map
 * using {@link java.util.Collections#synchronizedMap}. This class may throw
 * exceptions when accessed by concurrent threads without synchronization.
 * </p>
 *
 * @param <K> the type of the keys in this map
 * @param <V> the type of the values in this map
 *
 * @see java.lang.ref.Reference
 * @since 3.0 (previously in main package v2.1)
 */
public class ReferenceIdentityMap<K, V> extends AbstractReferenceMap<K, V> implements Serializable {

    /** Serialization version */
    private static final long serialVersionUID = -1266190134568365852L;

    /**
     * Constructs a new <code>ReferenceIdentityMap</code> that will
     * use hard references to keys and soft references to values.
     */
    public ReferenceIdentityMap() {
        super(ReferenceStrength.HARD, ReferenceStrength.SOFT, DEFAULT_CAPACITY,
                DEFAULT_LOAD_FACTOR, false);
    }

    /**
     * Constructs a new <code>ReferenceIdentityMap</code> that will
     * use the specified types of references.
     *
     * @param keyType  the type of reference to use for keys;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param valueType  the type of reference to use for values;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     */
    public ReferenceIdentityMap(final ReferenceStrength keyType, final ReferenceStrength valueType) {
        super(keyType, valueType, DEFAULT_CAPACITY, DEFAULT_LOAD_FACTOR, false);
    }

    /**
     * Constructs a new <code>ReferenceIdentityMap</code> that will
     * use the specified types of references.
     *
     * @param keyType  the type of reference to use for keys;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param valueType  the type of reference to use for values;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param purgeValues should the value be automatically purged when the
     *   key is garbage collected
     */
    public ReferenceIdentityMap(final ReferenceStrength keyType, final ReferenceStrength valueType,
            final boolean purgeValues) {
        super(keyType, valueType, DEFAULT_CAPACITY, DEFAULT_LOAD_FACTOR, purgeValues);
    }

    /**
     * Constructs a new <code>ReferenceIdentityMap</code> with the
     * specified reference types, load factor and initial capacity.
     *
     * @param keyType  the type of reference to use for keys;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param valueType  the type of reference to use for values;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param capacity  the initial capacity for the map
     * @param loadFactor  the load factor for the map
     */
    public ReferenceIdentityMap(final ReferenceStrength keyType, final ReferenceStrength valueType,
            final int capacity, final float loadFactor) {
        super(keyType, valueType, capacity, loadFactor, false);
    }

    /**
     * Constructs a new <code>ReferenceIdentityMap</code> with the
     * specified reference types, load factor and initial capacity.
     *
     * @param keyType  the type of reference to use for keys;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param valueType  the type of reference to use for values;
     *   must be {@link AbstractReferenceMap.ReferenceStrength#HARD HARD},
     *   {@link AbstractReferenceMap.ReferenceStrength#SOFT SOFT},
     *   {@link AbstractReferenceMap.ReferenceStrength#WEAK WEAK}
     * @param capacity  the initial capacity for the map
     * @param loadFactor  the load factor for the map
     * @param purgeValues  should the value be automatically purged when the
     *   key is garbage collected
     */
    public ReferenceIdentityMap(final ReferenceStrength keyType, final ReferenceStrength valueType,
            final int capacity, final float loadFactor, final boolean purgeValues) {
        super(keyType, valueType, capacity, loadFactor, purgeValues);
    }

    //-----------------------------------------------------------------------
    /**
     * Gets the hash code for the key specified.
     * <p>
     * This implementation uses the identity hash code.
     *
     * @param key  the key to get a hash code for
     * @return the hash code
     */
    @Override
    protected int hash(final Object key) {
        return System.identityHashCode(key);
    }

    /**
     * Gets the hash code for a MapEntry.
     * <p>
     * This implementation uses the identity hash code.
     *
     * @param key  the key to get a hash code for, may be null
     * @param value  the value to get a hash code for, may be null
     * @return the hash code, as per the MapEntry specification
     */
    @Override
    protected int hashEntry(final Object key, final Object value) {
        return System.identityHashCode(key) ^
               System.identityHashCode(value);
    }

    /**
     * Compares two keys for equals.
     * <p>
     * This implementation converts the key from the entry to a real reference
     * before comparison and uses <code>==</code>.
     *
     * @param key1  the first key to compare passed in from outside
     * @param key2  the second key extracted from the entry via <code>entry.key</code>
     * @return true if equal by identity
     */
    @Override
    protected boolean isEqualKey(final Object key1, Object key2) {
        key2 = isKeyType(ReferenceStrength.HARD) ? key2 : ((Reference<?>) key2).get();
        return key1 == key2;
    }

    /**
     * Compares two values for equals.
     * <p>
     * This implementation uses <code>==</code>.
     *
     * @param value1  the first value to compare passed in from outside
     * @param value2  the second value extracted from the entry via <code>getValue()</code>
     * @return true if equal by identity
     */
    @Override
    protected boolean isEqualValue(final Object value1, final Object value2) {
        return value1 == value2;
    }

    //-----------------------------------------------------------------------
    /**
     * Write the map out using a custom routine.
     *
     * @param out the output stream
     * @throws IOException if an error occurs while writing to the stream
     */
    private void writeObject(final ObjectOutputStream out) throws IOException {
        out.defaultWriteObject();
        doWriteObject(out);
    }

    /**
     * Read the map in using a custom routine.
     *
     * @param in the input stream
     * @throws IOException if an error occurs while reading from the stream
     * @throws ClassNotFoundException if an object read from the stream can not be loaded
     */
    private void readObject(final ObjectInputStream in) throws IOException, ClassNotFoundException {
        in.defaultReadObject();
        doReadObject(in);
    }

}
