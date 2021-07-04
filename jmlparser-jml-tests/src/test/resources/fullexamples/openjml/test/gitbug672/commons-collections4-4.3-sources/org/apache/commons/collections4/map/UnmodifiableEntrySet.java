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

import java.lang.reflect.Array;
import java.util.Collection;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.Unmodifiable;
import org.apache.commons.collections4.iterators.AbstractIteratorDecorator;
import org.apache.commons.collections4.keyvalue.AbstractMapEntryDecorator;
import org.apache.commons.collections4.set.AbstractSetDecorator;

/**
 * Decorates a map entry <code>Set</code> to ensure it can't be altered.
 * <p>
 * Attempts to modify it will result in an UnsupportedOperationException.
 *
 * @param <K> the type of the keys in the map
 * @param <V> the type of the values in the map
 *
 * @since 3.0
 */
public final class UnmodifiableEntrySet<K, V>
        extends AbstractSetDecorator<Map.Entry<K, V>> implements Unmodifiable {

    /** Serialization version */
    private static final long serialVersionUID = 1678353579659253473L;

    /**
     * Factory method to create an unmodifiable set of Map Entry objects.
     *
     * @param <K>  the key type
     * @param <V>  the value type
     * @param set  the set to decorate, must not be null
     * @return a new unmodifiable entry set
     * @throws NullPointerException if set is null
     * @since 4.0
     */
    public static <K, V> Set<Map.Entry<K, V>> unmodifiableEntrySet(final Set<Map.Entry<K, V>> set) {
        if (set instanceof Unmodifiable) {
            return set;
        }
        return new UnmodifiableEntrySet<>(set);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     *
     * @param set  the set to decorate, must not be null
     * @throws NullPointerException if set is null
     */
    private UnmodifiableEntrySet(final Set<Map.Entry<K, V>> set) {
        super(set);
    }

    //-----------------------------------------------------------------------
    @Override
    public boolean add(final Map.Entry<K, V> object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean addAll(final Collection<? extends Map.Entry<K, V>> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public void clear() {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean remove(final Object object) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean removeAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    @Override
    public boolean retainAll(final Collection<?> coll) {
        throw new UnsupportedOperationException();
    }

    //-----------------------------------------------------------------------
    @Override
    public Iterator<Map.Entry<K, V>> iterator() {
        return new UnmodifiableEntrySetIterator(decorated().iterator());
    }

    @Override
    @SuppressWarnings("unchecked")
    public Object[] toArray() {
        final Object[] array = decorated().toArray();
        for (int i = 0; i < array.length; i++) {
            array[i] = new UnmodifiableEntry((Map.Entry<K, V>) array[i]);
        }
        return array;
    }

    @Override
    @SuppressWarnings("unchecked")
    public <T> T[] toArray(final T[] array) {
        Object[] result = array;
        if (array.length > 0) {
            // we must create a new array to handle multi-threaded situations
            // where another thread could access data before we decorate it
            result = (Object[]) Array.newInstance(array.getClass().getComponentType(), 0);
        }
        result = decorated().toArray(result);
        for (int i = 0; i < result.length; i++) {
            result[i] = new UnmodifiableEntry((Map.Entry<K, V>) result[i]);
        }

        // check to see if result should be returned straight
        if (result.length > array.length) {
            return (T[]) result;
        }

        // copy back into input array to fulfill the method contract
        System.arraycopy(result, 0, array, 0, result.length);
        if (array.length > result.length) {
            array[result.length] = null;
        }
        return array;
    }

    //-----------------------------------------------------------------------
    /**
     * Implementation of an entry set iterator.
     */
    private class UnmodifiableEntrySetIterator extends AbstractIteratorDecorator<Map.Entry<K, V>> {

        protected UnmodifiableEntrySetIterator(final Iterator<Map.Entry<K, V>> iterator) {
            super(iterator);
        }

        @Override
        public Map.Entry<K, V> next() {
            return new UnmodifiableEntry(getIterator().next());
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Implementation of a map entry that is unmodifiable.
     */
    private class UnmodifiableEntry extends AbstractMapEntryDecorator<K, V> {

        protected UnmodifiableEntry(final Map.Entry<K, V> entry) {
            super(entry);
        }

        @Override
        public V setValue(final V obj) {
            throw new UnsupportedOperationException();
        }
    }

}
