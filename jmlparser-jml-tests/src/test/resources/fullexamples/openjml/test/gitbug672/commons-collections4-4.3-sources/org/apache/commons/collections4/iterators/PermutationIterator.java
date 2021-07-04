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
package org.apache.commons.collections4.iterators;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;

/**
 * This iterator creates permutations of an input collection, using the
 * Steinhaus-Johnson-Trotter algorithm (also called plain changes).
 * <p>
 * The iterator will return exactly n! permutations of the input collection.
 * The {@code remove()} operation is not supported, and will throw an
 * {@code UnsupportedOperationException}.
 * <p>
 * NOTE: in case an empty collection is provided, the iterator will
 * return exactly one empty list as result, as 0! = 1.
 *
 * @param <E>  the type of the objects being permuted
 *
 * @since 4.0
 */
public class PermutationIterator<E> implements Iterator<List<E>> {

    /**
     * Permutation is done on theses keys to handle equal objects.
     */
    private final int[] keys;

    /**
     * Mapping between keys and objects.
     */
    private final Map<Integer, E> objectMap;

    /**
     * Direction table used in the algorithm:
     * <ul>
     *   <li>false is left</li>
     *   <li>true is right</li>
     * </ul>
     */
    private final boolean[] direction;

    /**
     * Next permutation to return. When a permutation is requested
     * this instance is provided and the next one is computed.
     */
    private List<E> nextPermutation;

    /**
     * Standard constructor for this class.
     * @param coll  the collection to generate permutations for
     * @throws NullPointerException if coll is null
     */
    public PermutationIterator(final Collection<? extends E> coll) {
        if (coll == null) {
            throw new NullPointerException("The collection must not be null");
        }

        keys = new int[coll.size()];
        direction = new boolean[coll.size()];
        Arrays.fill(direction, false);
        int value = 1;
        objectMap = new HashMap<>();
        for (final E e : coll) {
            objectMap.put(Integer.valueOf(value), e);
            keys[value - 1] = value;
            value++;
        }
        nextPermutation = new ArrayList<>(coll);
    }

    /**
     * Indicates if there are more permutation available.
     * @return true if there are more permutations, otherwise false
     */
    @Override
    public boolean hasNext() {
        return nextPermutation != null;
    }

    /**
     * Returns the next permutation of the input collection.
     * @return a list of the permutator's elements representing a permutation
     * @throws NoSuchElementException if there are no more permutations
     */
    @Override
    public List<E> next() {
        if (!hasNext()) {
            throw new NoSuchElementException();
        }

        // find the largest mobile integer k
        int indexOfLargestMobileInteger = -1;
        int largestKey = -1;
        for (int i = 0; i < keys.length; i++) {
            if ((direction[i] && i < keys.length - 1 && keys[i] > keys[i + 1]) ||
                (!direction[i] && i > 0 && keys[i] > keys[i - 1])) {
                if (keys[i] > largestKey) { // NOPMD
                    largestKey = keys[i];
                    indexOfLargestMobileInteger = i;
                }
            }
        }
        if (largestKey == -1) {
            final List<E> toReturn = nextPermutation;
            nextPermutation = null;
            return toReturn;
        }

        // swap k and the adjacent integer it is looking at
        final int offset = direction[indexOfLargestMobileInteger] ? 1 : -1;
        final int tmpKey = keys[indexOfLargestMobileInteger];
        keys[indexOfLargestMobileInteger] = keys[indexOfLargestMobileInteger + offset];
        keys[indexOfLargestMobileInteger + offset] = tmpKey;
        final boolean tmpDirection = direction[indexOfLargestMobileInteger];
        direction[indexOfLargestMobileInteger] = direction[indexOfLargestMobileInteger + offset];
        direction[indexOfLargestMobileInteger + offset] = tmpDirection;

        // reverse the direction of all integers larger than k and build the result
        final List<E> nextP = new ArrayList<>();
        for (int i = 0; i < keys.length; i++) {
            if (keys[i] > largestKey) {
                direction[i] = !direction[i];
            }
            nextP.add(objectMap.get(Integer.valueOf(keys[i])));
        }
        final List<E> result = nextPermutation;
        nextPermutation = nextP;
        return result;
    }

    @Override
    public void remove() {
        throw new UnsupportedOperationException("remove() is not supported");
    }

}
