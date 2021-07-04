/*
 * Licensed to the Apache Software Foundation (ASF) under one or more contributor license
 * agreements. See the NOTICE file distributed with this work for additional information regarding
 * copyright ownership. The ASF licenses this file to You under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance with the License. You may obtain a
 * copy of the License at http://www.apache.org/licenses/LICENSE-2.0 Unless required by applicable
 * law or agreed to in writing, software distributed under the License is distributed on an "AS IS"
 * BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License
 * for the specific language governing permissions and limitations under the License.
 */
package org.apache.commons.collections4;

/**
 * An equation function, which determines equality between objects of type T.
 * <p>
 * It is the functional sibling of {@link java.util.Comparator}; {@link Equator} is to
 * {@link Object} as {@link java.util.Comparator} is to {@link java.lang.Comparable}.
 *
 * @param <T> the types of object this {@link Equator} can evaluate.
 * @since 4.0
 */
public interface Equator<T> {
    /**
     * Evaluates the two arguments for their equality.
     *
     * @param o1 the first object to be equated.
     * @param o2 the second object to be equated.
     * @return whether the two objects are equal.
     */
    boolean equate(T o1, T o2);

    /**
     * Calculates the hash for the object, based on the method of equality used in the equate
     * method. This is used for classes that delegate their {@link Object#equals(Object) equals(Object)} method to an
     * Equator (and so must also delegate their {@link Object#hashCode() hashCode()} method), or for implementations
     * of {@link org.apache.commons.collections4.map.HashedMap} that use an Equator for the key objects.
     *
     * @param o the object to calculate the hash for.
     * @return the hash of the object.
     */
    int hash(T o);
}
