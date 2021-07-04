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
package org.apache.commons.collections4.functors;

import java.io.Serializable;

import org.apache.commons.collections4.Equator;

/**
 * Default {@link Equator} implementation.
 *
 * @param <T>  the types of object this {@link Equator} can evaluate.
 * @since 4.0
 */
public class DefaultEquator<T> implements Equator<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 825802648423525485L;

    /** Static instance */
    @SuppressWarnings("rawtypes") // the static instance works for all types
    public static final DefaultEquator INSTANCE = new DefaultEquator<>();

    /**
     * Hashcode used for <code>null</code> objects.
     */
    public static final int HASHCODE_NULL = -1;

    /**
     * Factory returning the typed singleton instance.
     *
     * @param <T>  the object type
     * @return the singleton instance
     */
    @SuppressWarnings("unchecked") // the static instance works for all types
    public static <T> DefaultEquator<T> defaultEquator() {
        return DefaultEquator.INSTANCE;
    }

    /**
     * Restricted constructor.
     */
    private DefaultEquator() {
        super();
    }

    /**
     * {@inheritDoc} Delegates to {@link Object#equals(Object)}.
     */
    @Override
    public boolean equate(final T o1, final T o2) {
        return o1 == o2 || o1 != null && o1.equals(o2);
    }

    /**
     * {@inheritDoc}
     *
     * @return <code>o.hashCode()</code> if <code>o</code> is non-
     *         <code>null</code>, else {@link #HASHCODE_NULL}.
     */
    @Override
    public int hash(final T o) {
        return o == null ? HASHCODE_NULL : o.hashCode();
    }

    private Object readResolve() {
        return INSTANCE;
    }

}
