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
package org.apache.commons.collections4;

import java.util.Collection;
import java.util.Comparator;

import org.apache.commons.collections4.comparators.BooleanComparator;
import org.apache.commons.collections4.comparators.ComparableComparator;
import org.apache.commons.collections4.comparators.ComparatorChain;
import org.apache.commons.collections4.comparators.NullComparator;
import org.apache.commons.collections4.comparators.ReverseComparator;
import org.apache.commons.collections4.comparators.TransformingComparator;

/**
 * Provides convenient static utility methods for <Code>Comparator</Code>
 * objects.
 * <p>
 * Most of the functionality in this class can also be found in the
 * <code>comparators</code> package. This class merely provides a
 * convenient central place if you have use for more than one class
 * in the <code>comparators</code> subpackage.
 *
 * @since 2.1
 */
public class ComparatorUtils {

    /**
     * ComparatorUtils should not normally be instantiated.
     */
    private ComparatorUtils() {}

    /**
     * Comparator for natural sort order.
     *
     * @see ComparableComparator#comparableComparator()
     */
    @SuppressWarnings({ "rawtypes", "unchecked" }) // explicit type needed for Java 1.5 compilation
    public static final Comparator NATURAL_COMPARATOR = ComparableComparator.<Comparable>comparableComparator();

    /**
     * Gets a comparator that uses the natural order of the objects.
     *
     * @param <E>  the object type to compare
     * @return  a comparator which uses natural order
     */
    @SuppressWarnings("unchecked")
    public static <E extends Comparable<? super E>> Comparator<E> naturalComparator() {
        return NATURAL_COMPARATOR;
    }

    /**
     * Gets a comparator that compares using an array of {@link Comparator}s, applied
     * in sequence until one returns not equal or the array is exhausted.
     *
     * @param <E>  the object type to compare
     * @param comparators  the comparators to use, not null or empty or containing nulls
     * @return a {@link ComparatorChain} formed from the input comparators
     * @throws NullPointerException if comparators array is null or contains a null
     * @see ComparatorChain
     */
    public static <E> Comparator<E> chainedComparator(final Comparator<E>... comparators) {
        final ComparatorChain<E> chain = new ComparatorChain<>();
        for (final Comparator<E> comparator : comparators) {
            if (comparator == null) {
                throw new NullPointerException("Comparator cannot be null");
            }
            chain.addComparator(comparator);
        }
        return chain;
    }

    /**
     * Gets a comparator that compares using a collection of {@link Comparator}s,
     * applied in (default iterator) sequence until one returns not equal or the
     * collection is exhausted.
     *
     * @param <E>  the object type to compare
     * @param comparators  the comparators to use, not null or empty or containing nulls
     * @return a {@link ComparatorChain} formed from the input comparators
     * @throws NullPointerException if comparators collection is null or contains a null
     * @throws ClassCastException if the comparators collection contains the wrong object type
     * @see ComparatorChain
     */
    @SuppressWarnings("unchecked")
    public static <E> Comparator<E> chainedComparator(final Collection<Comparator<E>> comparators) {
        return chainedComparator(
            (Comparator<E>[]) comparators.toArray(new Comparator[comparators.size()])
        );
    }

    /**
     * Gets a comparator that reverses the order of the given comparator.
     *
     * @param <E>  the object type to compare
     * @param comparator  the comparator to reverse
     * @return  a comparator that reverses the order of the input comparator
     * @see ReverseComparator
     */
    public static <E> Comparator<E> reversedComparator(final Comparator<E> comparator) {
        return new ReverseComparator<>(comparator);
    }

    /**
     * Gets a Comparator that can sort Boolean objects.
     * <p>
     * The parameter specifies whether true or false is sorted first.
     * <p>
     * The comparator throws NullPointerException if a null value is compared.
     *
     * @param trueFirst  when <code>true</code>, sort
     *        <code>true</code> {@link Boolean}s before
     *        <code>false</code> {@link Boolean}s.
     * @return  a comparator that sorts booleans
     */
    public static Comparator<Boolean> booleanComparator(final boolean trueFirst) {
        return BooleanComparator.booleanComparator(trueFirst);
    }

    /**
     * Gets a Comparator that controls the comparison of <code>null</code> values.
     * <p>
     * The returned comparator will consider a null value to be less than
     * any nonnull value, and equal to any other null value.  Two nonnull
     * values will be evaluated with the given comparator.
     *
     * @param <E>  the object type to compare
     * @param comparator the comparator that wants to allow nulls
     * @return  a version of that comparator that allows nulls
     * @see NullComparator
     */
    @SuppressWarnings("unchecked")
    public static <E> Comparator<E> nullLowComparator(Comparator<E> comparator) {
        if (comparator == null) {
            comparator = NATURAL_COMPARATOR;
        }
        return new NullComparator<>(comparator, false);
    }

    /**
     * Gets a Comparator that controls the comparison of <code>null</code> values.
     * <p>
     * The returned comparator will consider a null value to be greater than
     * any nonnull value, and equal to any other null value.  Two nonnull
     * values will be evaluated with the given comparator.
     *
     * @param <E>  the object type to compare
     * @param comparator the comparator that wants to allow nulls
     * @return  a version of that comparator that allows nulls
     * @see NullComparator
     */
    @SuppressWarnings("unchecked")
    public static <E> Comparator<E> nullHighComparator(Comparator<E> comparator) {
        if (comparator == null) {
            comparator = NATURAL_COMPARATOR;
        }
        return new NullComparator<>(comparator, true);
    }

    /**
     * Gets a Comparator that passes transformed objects to the given comparator.
     * <p>
     * Objects passed to the returned comparator will first be transformed
     * by the given transformer before they are compared by the given
     * comparator.
     *
     * @param <I>  the input object type of the transformed comparator
     * @param <O>  the object type of the decorated comparator
     * @param comparator  the sort order to use
     * @param transformer  the transformer to use
     * @return  a comparator that transforms its input objects before comparing them
     * @see  TransformingComparator
     */
    @SuppressWarnings("unchecked")
    public static <I, O> Comparator<I> transformedComparator(Comparator<O> comparator,
            final Transformer<? super I, ? extends O> transformer) {

        if (comparator == null) {
            comparator = NATURAL_COMPARATOR;
        }
        return new TransformingComparator<>(transformer, comparator);
    }

    /**
     * Returns the smaller of the given objects according to the given
     * comparator, returning the second object if the comparator
     * returns equal.
     *
     * @param <E>  the object type to compare
     * @param o1  the first object to compare
     * @param o2  the second object to compare
     * @param comparator  the sort order to use
     * @return  the smaller of the two objects
     */
    @SuppressWarnings("unchecked")
    public static <E> E min(final E o1, final E o2, Comparator<E> comparator) {
        if (comparator == null) {
            comparator = NATURAL_COMPARATOR;
        }
        final int c = comparator.compare(o1, o2);
        return c < 0 ? o1 : o2;
    }

    /**
     * Returns the larger of the given objects according to the given
     * comparator, returning the second object if the comparator
     * returns equal.
     *
     * @param <E>  the object type to compare
     * @param o1  the first object to compare
     * @param o2  the second object to compare
     * @param comparator  the sort order to use
     * @return  the larger of the two objects
     */
    @SuppressWarnings("unchecked")
    public static <E> E max(final E o1, final E o2, Comparator<E> comparator) {
        if (comparator == null) {
            comparator = NATURAL_COMPARATOR;
        }
        final int c = comparator.compare(o1, o2);
        return c > 0 ? o1 : o2;
    }

}
