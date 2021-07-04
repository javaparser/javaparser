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
package org.apache.commons.collections4.comparators;

import java.io.Serializable;
import java.util.Comparator;

import org.apache.commons.collections4.ComparatorUtils;
import org.apache.commons.collections4.Transformer;

/**
 * Decorates another Comparator with transformation behavior. That is, the
 * return value from the transform operation will be passed to the decorated
 * {@link Comparator#compare(Object,Object) compare} method.
 * <p>
 * This class is Serializable from Commons Collections 4.0.
 *
 * @param <I> the input type to the transformer
 * @param <O> the output type from the transformer
 *
 * @since 2.1
 *
 * @see org.apache.commons.collections4.Transformer
 * @see org.apache.commons.collections4.comparators.ComparableComparator
 */
public class TransformingComparator<I, O> implements Comparator<I>, Serializable {

    /** Serialization version from Collections 4.0. */
    private static final long serialVersionUID = 3456940356043606220L;

    /** The decorated comparator. */
    private final Comparator<O> decorated;
    /** The transformer being used. */
    private final Transformer<? super I, ? extends O> transformer;

    //-----------------------------------------------------------------------
    /**
     * Constructs an instance with the given Transformer and a
     * {@link ComparableComparator ComparableComparator}.
     *
     * @param transformer what will transform the arguments to <code>compare</code>
     */
    @SuppressWarnings("unchecked")
    public TransformingComparator(final Transformer<? super I, ? extends O> transformer) {
        this(transformer, ComparatorUtils.NATURAL_COMPARATOR);
    }

    /**
     * Constructs an instance with the given Transformer and Comparator.
     *
     * @param transformer  what will transform the arguments to <code>compare</code>
     * @param decorated  the decorated Comparator
     */
    public TransformingComparator(final Transformer<? super I, ? extends O> transformer,
                                  final Comparator<O> decorated) {
        this.decorated = decorated;
        this.transformer = transformer;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns the result of comparing the values from the transform operation.
     *
     * @param obj1  the first object to transform then compare
     * @param obj2  the second object to transform then compare
     * @return negative if obj1 is less, positive if greater, zero if equal
     */
    @Override
    public int compare(final I obj1, final I obj2) {
        final O value1 = this.transformer.transform(obj1);
        final O value2 = this.transformer.transform(obj2);
        return this.decorated.compare(value1, value2);
    }

    //-----------------------------------------------------------------------
    /**
     * Implement a hash code for this comparator that is consistent with
     * {@link #equals(Object) equals}.
     *
     * @return a hash code for this comparator.
     */
    @Override
    public int hashCode() {
        int total = 17;
        total = total*37 + (decorated == null ? 0 : decorated.hashCode());
        total = total*37 + (transformer == null ? 0 : transformer.hashCode());
        return total;
    }

    /**
     * Returns <code>true</code> iff <i>that</i> Object is
     * is a {@link Comparator} whose ordering is known to be
     * equivalent to mine.
     * <p>
     * This implementation returns <code>true</code>
     * iff <code><i>that</i></code> is a {@link TransformingComparator}
     * whose attributes are equal to mine.
     *
     * @param object  the object to compare to
     * @return true if equal
     */
    @Override
    public boolean equals(final Object object) {
        if (this == object) {
            return true;
        }
        if (null == object) {
            return false;
        }
        if (object.getClass().equals(this.getClass())) {
            final TransformingComparator<?, ?> comp = (TransformingComparator<?, ?>) object;
            return (null == decorated ? null == comp.decorated : decorated.equals(comp.decorated)) &&
                   (null == transformer ? null == comp.transformer : transformer.equals(comp.transformer));
        }
        return false;
    }

}

