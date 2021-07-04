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

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Enumeration;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;

import org.apache.commons.collections4.bag.HashBag;
import org.apache.commons.collections4.collection.PredicatedCollection;
import org.apache.commons.collections4.collection.SynchronizedCollection;
import org.apache.commons.collections4.collection.TransformedCollection;
import org.apache.commons.collections4.collection.UnmodifiableBoundedCollection;
import org.apache.commons.collections4.collection.UnmodifiableCollection;
import org.apache.commons.collections4.functors.TruePredicate;
import org.apache.commons.collections4.iterators.CollatingIterator;
import org.apache.commons.collections4.iterators.PermutationIterator;

/**
 * Provides utility methods and decorators for {@link Collection} instances.
 * <p>
 * Various utility methods might put the input objects into a Set/Map/Bag. In case
 * the input objects override {@link Object#equals(Object)}, it is mandatory that
 * the general contract of the {@link Object#hashCode()} method is maintained.
 * <p>
 * NOTE: From 4.0, method parameters will take {@link Iterable} objects when possible.
 *
 * @since 1.0
 */
public class CollectionUtils {

    /**
     * Helper class to easily access cardinality properties of two collections.
     * @param <O>  the element type
     */
    private static class CardinalityHelper<O> {

        /** Contains the cardinality for each object in collection A. */
        final Map<O, Integer> cardinalityA;

        /** Contains the cardinality for each object in collection B. */
        final Map<O, Integer> cardinalityB;

        /**
         * Create a new CardinalityHelper for two collections.
         * @param a  the first collection
         * @param b  the second collection
         */
        public CardinalityHelper(final Iterable<? extends O> a, final Iterable<? extends O> b) {
            cardinalityA = CollectionUtils.<O>getCardinalityMap(a);
            cardinalityB = CollectionUtils.<O>getCardinalityMap(b);
        }

        /**
         * Returns the maximum frequency of an object.
         * @param obj  the object
         * @return the maximum frequency of the object
         */
        public final int max(final Object obj) {
            return Math.max(freqA(obj), freqB(obj));
        }

        /**
         * Returns the minimum frequency of an object.
         * @param obj  the object
         * @return the minimum frequency of the object
         */
        public final int min(final Object obj) {
            return Math.min(freqA(obj), freqB(obj));
        }

        /**
         * Returns the frequency of this object in collection A.
         * @param obj  the object
         * @return the frequency of the object in collection A
         */
        public int freqA(final Object obj) {
            return getFreq(obj, cardinalityA);
        }

        /**
         * Returns the frequency of this object in collection B.
         * @param obj  the object
         * @return the frequency of the object in collection B
         */
        public int freqB(final Object obj) {
            return getFreq(obj, cardinalityB);
        }

        private int getFreq(final Object obj, final Map<?, Integer> freqMap) {
            final Integer count = freqMap.get(obj);
            if (count != null) {
                return count.intValue();
            }
            return 0;
        }
    }

    /**
     * Helper class for set-related operations, e.g. union, subtract, intersection.
     * @param <O>  the element type
     */
    private static class SetOperationCardinalityHelper<O> extends CardinalityHelper<O> implements Iterable<O> {

        /** Contains the unique elements of the two collections. */
        private final Set<O> elements;

        /** Output collection. */
        private final List<O> newList;

        /**
         * Create a new set operation helper from the two collections.
         * @param a  the first collection
         * @param b  the second collection
         */
        public SetOperationCardinalityHelper(final Iterable<? extends O> a, final Iterable<? extends O> b) {
            super(a, b);
            elements = new HashSet<>();
            addAll(elements, a);
            addAll(elements, b);
            // the resulting list must contain at least each unique element, but may grow
            newList = new ArrayList<>(elements.size());
        }

        @Override
        public Iterator<O> iterator() {
            return elements.iterator();
        }

        /**
         * Add the object {@code count} times to the result collection.
         * @param obj  the object to add
         * @param count  the count
         */
        public void setCardinality(final O obj, final int count) {
            for (int i = 0; i < count; i++) {
                newList.add(obj);
            }
        }

        /**
         * Returns the resulting collection.
         * @return the result
         */
        public Collection<O> list() {
            return newList;
        }

    }

    /**
     * An empty unmodifiable collection.
     * The JDK provides empty Set and List implementations which could be used for
     * this purpose. However they could be cast to Set or List which might be
     * undesirable. This implementation only implements Collection.
     */
    @SuppressWarnings("rawtypes") // we deliberately use the raw type here
    public static final Collection EMPTY_COLLECTION = Collections.emptyList();

    /**
     * <code>CollectionUtils</code> should not normally be instantiated.
     */
    private CollectionUtils() {}

    /**
     * Returns the immutable EMPTY_COLLECTION with generic type safety.
     *
     * @see #EMPTY_COLLECTION
     * @since 4.0
     * @param <T> the element type
     * @return immutable empty collection
     */
    @SuppressWarnings("unchecked") // OK, empty collection is compatible with any type
    public static <T> Collection<T> emptyCollection() {
        return EMPTY_COLLECTION;
    }

    /**
     * Returns an immutable empty collection if the argument is <code>null</code>,
     * or the argument itself otherwise.
     *
     * @param <T> the element type
     * @param collection the collection, possibly <code>null</code>
     * @return an empty collection if the argument is <code>null</code>
     */
    public static <T> Collection<T> emptyIfNull(final Collection<T> collection) {
        return collection == null ? CollectionUtils.<T>emptyCollection() : collection;
    }

    /**
     * Returns a {@link Collection} containing the union of the given
     * {@link Iterable}s.
     * <p>
     * The cardinality of each element in the returned {@link Collection} will
     * be equal to the maximum of the cardinality of that element in the two
     * given {@link Iterable}s.
     *
     * @param a the first collection, must not be null
     * @param b the second collection, must not be null
     * @param <O> the generic type that is able to represent the types contained
     *        in both input collections.
     * @return the union of the two collections
     * @see Collection#addAll
     */
    public static <O> Collection<O> union(final Iterable<? extends O> a, final Iterable<? extends O> b) {
        final SetOperationCardinalityHelper<O> helper = new SetOperationCardinalityHelper<>(a, b);
        for (final O obj : helper) {
            helper.setCardinality(obj, helper.max(obj));
        }
        return helper.list();
    }

    /**
     * Returns a {@link Collection} containing the intersection of the given
     * {@link Iterable}s.
     * <p>
     * The cardinality of each element in the returned {@link Collection} will
     * be equal to the minimum of the cardinality of that element in the two
     * given {@link Iterable}s.
     *
     * @param a the first collection, must not be null
     * @param b the second collection, must not be null
     * @param <O> the generic type that is able to represent the types contained
     *        in both input collections.
     * @return the intersection of the two collections
     * @see Collection#retainAll
     * @see #containsAny
     */
    public static <O> Collection<O> intersection(final Iterable<? extends O> a, final Iterable<? extends O> b) {
        final SetOperationCardinalityHelper<O> helper = new SetOperationCardinalityHelper<>(a, b);
        for (final O obj : helper) {
            helper.setCardinality(obj, helper.min(obj));
        }
        return helper.list();
    }

    /**
     * Returns a {@link Collection} containing the exclusive disjunction
     * (symmetric difference) of the given {@link Iterable}s.
     * <p>
     * The cardinality of each element <i>e</i> in the returned
     * {@link Collection} will be equal to
     * <code>max(cardinality(<i>e</i>,<i>a</i>),cardinality(<i>e</i>,<i>b</i>)) - min(cardinality(<i>e</i>,<i>a</i>),
     * cardinality(<i>e</i>,<i>b</i>))</code>.
     * <p>
     * This is equivalent to
     * {@code {@link #subtract subtract}({@link #union union(a,b)},{@link #intersection intersection(a,b)})}
     * or
     * {@code {@link #union union}({@link #subtract subtract(a,b)},{@link #subtract subtract(b,a)})}.

     * @param a the first collection, must not be null
     * @param b the second collection, must not be null
     * @param <O> the generic type that is able to represent the types contained
     *        in both input collections.
     * @return the symmetric difference of the two collections
     */
    public static <O> Collection<O> disjunction(final Iterable<? extends O> a, final Iterable<? extends O> b) {
        final SetOperationCardinalityHelper<O> helper = new SetOperationCardinalityHelper<>(a, b);
        for (final O obj : helper) {
            helper.setCardinality(obj, helper.max(obj) - helper.min(obj));
        }
        return helper.list();
    }

    /**
     * Returns a new {@link Collection} containing {@code <i>a</i> - <i>b</i>}.
     * The cardinality of each element <i>e</i> in the returned {@link Collection}
     * will be the cardinality of <i>e</i> in <i>a</i> minus the cardinality
     * of <i>e</i> in <i>b</i>, or zero, whichever is greater.
     *
     * @param a  the collection to subtract from, must not be null
     * @param b  the collection to subtract, must not be null
     * @param <O> the generic type that is able to represent the types contained
     *        in both input collections.
     * @return a new collection with the results
     * @see Collection#removeAll
     */
    public static <O> Collection<O> subtract(final Iterable<? extends O> a, final Iterable<? extends O> b) {
        final Predicate<O> p = TruePredicate.truePredicate();
        return subtract(a, b, p);
    }

    /**
     * Returns a new {@link Collection} containing <i>a</i> minus a subset of
     * <i>b</i>.  Only the elements of <i>b</i> that satisfy the predicate
     * condition, <i>p</i> are subtracted from <i>a</i>.
     *
     * <p>The cardinality of each element <i>e</i> in the returned {@link Collection}
     * that satisfies the predicate condition will be the cardinality of <i>e</i> in <i>a</i>
     * minus the cardinality of <i>e</i> in <i>b</i>, or zero, whichever is greater.</p>
     * <p>The cardinality of each element <i>e</i> in the returned {@link Collection} that does <b>not</b>
     * satisfy the predicate condition will be equal to the cardinality of <i>e</i> in <i>a</i>.</p>
     *
     * @param a  the collection to subtract from, must not be null
     * @param b  the collection to subtract, must not be null
     * @param p  the condition used to determine which elements of <i>b</i> are
     *        subtracted.
     * @param <O> the generic type that is able to represent the types contained
     *        in both input collections.
     * @return a new collection with the results
     * @since 4.0
     * @see Collection#removeAll
     */
    public static <O> Collection<O> subtract(final Iterable<? extends O> a,
                                             final Iterable<? extends O> b,
                                             final Predicate<O> p) {
        final ArrayList<O> list = new ArrayList<>();
        final HashBag<O> bag = new HashBag<>();
        for (final O element : b) {
            if (p.evaluate(element)) {
                bag.add(element);
            }
        }
        for (final O element : a) {
            if (!bag.remove(element, 1)) {
                list.add(element);
            }
        }
        return list;
    }

    /**
     * Returns <code>true</code> iff all elements of {@code coll2} are also contained
     * in {@code coll1}. The cardinality of values in {@code coll2} is not taken into account,
     * which is the same behavior as {@link Collection#containsAll(Collection)}.
     * <p>
     * In other words, this method returns <code>true</code> iff the
     * {@link #intersection} of <i>coll1</i> and <i>coll2</i> has the same cardinality as
     * the set of unique values from {@code coll2}. In case {@code coll2} is empty, {@code true}
     * will be returned.
     * <p>
     * This method is intended as a replacement for {@link Collection#containsAll(Collection)}
     * with a guaranteed runtime complexity of {@code O(n + m)}. Depending on the type of
     * {@link Collection} provided, this method will be much faster than calling
     * {@link Collection#containsAll(Collection)} instead, though this will come at the
     * cost of an additional space complexity O(n).
     *
     * @param coll1  the first collection, must not be null
     * @param coll2  the second collection, must not be null
     * @return <code>true</code> iff the intersection of the collections has the same cardinality
     *   as the set of unique elements from the second collection
     * @since 4.0
     */
    public static boolean containsAll(final Collection<?> coll1, final Collection<?> coll2) {
        if (coll2.isEmpty()) {
            return true;
        }
        final Iterator<?> it = coll1.iterator();
        final Set<Object> elementsAlreadySeen = new HashSet<>();
        for (final Object nextElement : coll2) {
            if (elementsAlreadySeen.contains(nextElement)) {
                continue;
            }

            boolean foundCurrentElement = false;
            while (it.hasNext()) {
                final Object p = it.next();
                elementsAlreadySeen.add(p);
                if (nextElement == null ? p == null : nextElement.equals(p)) {
                    foundCurrentElement = true;
                    break;
                }
            }

            if (!foundCurrentElement) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns <code>true</code> iff at least one element is in both collections.
     * <p>
     * In other words, this method returns <code>true</code> iff the
     * {@link #intersection} of <i>coll1</i> and <i>coll2</i> is not empty.
     *
     * @param <T> the type of object to lookup in <code>coll1</code>.
     * @param coll1  the first collection, must not be null
     * @param coll2  the second collection, must not be null
     * @return <code>true</code> iff the intersection of the collections is non-empty
     * @since 4.2
     * @see #intersection
     */
    public static <T> boolean containsAny(final Collection<?> coll1, @SuppressWarnings("unchecked") final T... coll2) {
        if (coll1.size() < coll2.length) {
            for (final Object aColl1 : coll1) {
                if (ArrayUtils.contains(coll2, aColl1)) {
                    return true;
                }
            }
        } else {
            for (final Object aColl2 : coll2) {
                if (coll1.contains(aColl2)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns <code>true</code> iff at least one element is in both collections.
     * <p>
     * In other words, this method returns <code>true</code> iff the
     * {@link #intersection} of <i>coll1</i> and <i>coll2</i> is not empty.
     *
     * @param coll1  the first collection, must not be null
     * @param coll2  the second collection, must not be null
     * @return <code>true</code> iff the intersection of the collections is non-empty
     * @since 2.1
     * @see #intersection
     */
    public static boolean containsAny(final Collection<?> coll1, final Collection<?> coll2) {
        if (coll1.size() < coll2.size()) {
            for (final Object aColl1 : coll1) {
                if (coll2.contains(aColl1)) {
                    return true;
                }
            }
        } else {
            for (final Object aColl2 : coll2) {
                if (coll1.contains(aColl2)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Returns a {@link Map} mapping each unique element in the given
     * {@link Collection} to an {@link Integer} representing the number
     * of occurrences of that element in the {@link Collection}.
     * <p>
     * Only those elements present in the collection will appear as
     * keys in the map.
     *
     * @param <O>  the type of object in the returned {@link Map}. This is a super type of &lt;I&gt;.
     * @param coll  the collection to get the cardinality map for, must not be null
     * @return the populated cardinality map
     */
    public static <O> Map<O, Integer> getCardinalityMap(final Iterable<? extends O> coll) {
        final Map<O, Integer> count = new HashMap<>();
        for (final O obj : coll) {
            final Integer c = count.get(obj);
            if (c == null) {
                count.put(obj, Integer.valueOf(1));
            } else {
                count.put(obj, Integer.valueOf(c.intValue() + 1));
            }
        }
        return count;
    }

    /**
     * Returns {@code true} iff <i>a</i> is a sub-collection of <i>b</i>,
     * that is, iff the cardinality of <i>e</i> in <i>a</i> is less than or
     * equal to the cardinality of <i>e</i> in <i>b</i>, for each element <i>e</i>
     * in <i>a</i>.
     *
     * @param a the first (sub?) collection, must not be null
     * @param b the second (super?) collection, must not be null
     * @return <code>true</code> iff <i>a</i> is a sub-collection of <i>b</i>
     * @see #isProperSubCollection
     * @see Collection#containsAll
     */
    public static boolean isSubCollection(final Collection<?> a, final Collection<?> b) {
        final CardinalityHelper<Object> helper = new CardinalityHelper<>(a, b);
        for (final Object obj : a) {
            if (helper.freqA(obj) > helper.freqB(obj)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns {@code true} iff <i>a</i> is a <i>proper</i> sub-collection of <i>b</i>,
     * that is, iff the cardinality of <i>e</i> in <i>a</i> is less
     * than or equal to the cardinality of <i>e</i> in <i>b</i>,
     * for each element <i>e</i> in <i>a</i>, and there is at least one
     * element <i>f</i> such that the cardinality of <i>f</i> in <i>b</i>
     * is strictly greater than the cardinality of <i>f</i> in <i>a</i>.
     * <p>
     * The implementation assumes
     * <ul>
     *    <li><code>a.size()</code> and <code>b.size()</code> represent the
     *    total cardinality of <i>a</i> and <i>b</i>, resp. </li>
     *    <li><code>a.size() &lt; Integer.MAXVALUE</code></li>
     * </ul>
     *
     * @param a  the first (sub?) collection, must not be null
     * @param b  the second (super?) collection, must not be null
     * @return <code>true</code> iff <i>a</i> is a <i>proper</i> sub-collection of <i>b</i>
     * @see #isSubCollection
     * @see Collection#containsAll
     */
    public static boolean isProperSubCollection(final Collection<?> a, final Collection<?> b) {
        return a.size() < b.size() && CollectionUtils.isSubCollection(a, b);
    }

    /**
     * Returns {@code true} iff the given {@link Collection}s contain
     * exactly the same elements with exactly the same cardinalities.
     * <p>
     * That is, iff the cardinality of <i>e</i> in <i>a</i> is
     * equal to the cardinality of <i>e</i> in <i>b</i>,
     * for each element <i>e</i> in <i>a</i> or <i>b</i>.
     *
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @return <code>true</code> iff the collections contain the same elements with the same cardinalities.
     */
    public static boolean isEqualCollection(final Collection<?> a, final Collection<?> b) {
        if(a.size() != b.size()) {
            return false;
        }
        final CardinalityHelper<Object> helper = new CardinalityHelper<>(a, b);
        if(helper.cardinalityA.size() != helper.cardinalityB.size()) {
            return false;
        }
        for( final Object obj : helper.cardinalityA.keySet()) {
            if(helper.freqA(obj) != helper.freqB(obj)) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns {@code true} iff the given {@link Collection}s contain
     * exactly the same elements with exactly the same cardinalities.
     * <p>
     * That is, iff the cardinality of <i>e</i> in <i>a</i> is
     * equal to the cardinality of <i>e</i> in <i>b</i>,
     * for each element <i>e</i> in <i>a</i> or <i>b</i>.
     * <p>
     * <b>Note:</b> from version 4.1 onwards this method requires the input
     * collections and equator to be of compatible type (using bounded wildcards).
     * Providing incompatible arguments (e.g. by casting to their rawtypes)
     * will result in a {@code ClassCastException} thrown at runtime.
     *
     * @param <E>  the element type
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @param equator  the Equator used for testing equality
     * @return <code>true</code> iff the collections contain the same elements with the same cardinalities.
     * @throws NullPointerException if the equator is null
     * @since 4.0
     */
    public static <E> boolean isEqualCollection(final Collection<? extends E> a,
                                                final Collection<? extends E> b,
                                                final Equator<? super E> equator) {
        if (equator == null) {
            throw new NullPointerException("Equator must not be null.");
        }

        if(a.size() != b.size()) {
            return false;
        }

        @SuppressWarnings({ "unchecked", "rawtypes" })
        final Transformer<E, ?> transformer = new Transformer() {
            @Override
            public EquatorWrapper<?> transform(final Object input) {
                return new EquatorWrapper(equator, input);
            }
        };

        return isEqualCollection(collect(a, transformer), collect(b, transformer));
    }

    /**
     * Wraps another object and uses the provided Equator to implement
     * {@link #equals(Object)} and {@link #hashCode()}.
     * <p>
     * This class can be used to store objects into a Map.
     *
     * @param <O>  the element type
     * @since 4.0
     */
    private static class EquatorWrapper<O> {
        private final Equator<? super O> equator;
        private final O object;

        public EquatorWrapper(final Equator<? super O> equator, final O object) {
            this.equator = equator;
            this.object = object;
        }

        public O getObject() {
            return object;
        }

        @Override
        public boolean equals(final Object obj) {
            if (!(obj instanceof EquatorWrapper)) {
                return false;
            }
            @SuppressWarnings("unchecked")
            final EquatorWrapper<O> otherObj = (EquatorWrapper<O>) obj;
            return equator.equate(object, otherObj.getObject());
        }

        @Override
        public int hashCode() {
            return equator.hash(object);
        }
    }

    /**
     * Returns the number of occurrences of <i>obj</i> in <i>coll</i>.
     *
     * @param obj the object to find the cardinality of
     * @param coll the {@link Iterable} to search
     * @param <O> the type of object that the {@link Iterable} may contain.
     * @return the number of occurrences of obj in coll
     * @throws NullPointerException if coll is null
     * @deprecated since 4.1, use {@link IterableUtils#frequency(Iterable, Object)} instead.
     *   Be aware that the order of parameters has changed.
     */
    @Deprecated
    public static <O> int cardinality(final O obj, final Iterable<? super O> coll) {
        if (coll == null) {
            throw new NullPointerException("coll must not be null.");
        }
        return IterableUtils.frequency(coll, obj);
    }

    /**
     * Finds the first element in the given collection which matches the given predicate.
     * <p>
     * If the input collection or predicate is null, or no element of the collection
     * matches the predicate, null is returned.
     *
     * @param <T>  the type of object the {@link Iterable} contains
     * @param collection  the collection to search, may be null
     * @param predicate  the predicate to use, may be null
     * @return the first element of the collection which matches the predicate or null if none could be found
     * @deprecated since 4.1, use {@link IterableUtils#find(Iterable, Predicate)} instead
     */
    @Deprecated
    public static <T> T find(final Iterable<T> collection, final Predicate<? super T> predicate) {
        return predicate != null ? IterableUtils.find(collection, predicate) : null;
    }

    /**
     * Executes the given closure on each element in the collection.
     * <p>
     * If the input collection or closure is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Iterable} contains
     * @param <C>  the closure type
     * @param collection  the collection to get the input from, may be null
     * @param closure  the closure to perform, may be null
     * @return closure
     * @deprecated since 4.1, use {@link IterableUtils#forEach(Iterable, Closure)} instead
     */
    @Deprecated
    public static <T, C extends Closure<? super T>> C forAllDo(final Iterable<T> collection, final C closure) {
        if (closure != null) {
            IterableUtils.forEach(collection, closure);
        }
        return closure;
    }

    /**
     * Executes the given closure on each element in the collection.
     * <p>
     * If the input collection or closure is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Iterator} contains
     * @param <C>  the closure type
     * @param iterator  the iterator to get the input from, may be null
     * @param closure  the closure to perform, may be null
     * @return closure
     * @since 4.0
     * @deprecated since 4.1, use {@link IteratorUtils#forEach(Iterator, Closure)} instead
     */
    @Deprecated
    public static <T, C extends Closure<? super T>> C forAllDo(final Iterator<T> iterator, final C closure) {
        if (closure != null) {
            IteratorUtils.forEach(iterator, closure);
        }
        return closure;
    }

    /**
     * Executes the given closure on each but the last element in the collection.
     * <p>
     * If the input collection or closure is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Iterable} contains
     * @param <C>  the closure type
     * @param collection  the collection to get the input from, may be null
     * @param closure  the closure to perform, may be null
     * @return the last element in the collection, or null if either collection or closure is null
     * @since 4.0
     * @deprecated since 4.1, use {@link IterableUtils#forEachButLast(Iterable, Closure)} instead
     */
    @Deprecated
    public static <T, C extends Closure<? super T>> T forAllButLastDo(final Iterable<T> collection,
                                                                      final C closure) {
        return closure != null ? IterableUtils.forEachButLast(collection, closure) : null;
    }

    /**
     * Executes the given closure on each but the last element in the collection.
     * <p>
     * If the input collection or closure is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Collection} contains
     * @param <C>  the closure type
     * @param iterator  the iterator to get the input from, may be null
     * @param closure  the closure to perform, may be null
     * @return the last element in the collection, or null if either iterator or closure is null
     * @since 4.0
     * @deprecated since 4.1, use {@link IteratorUtils#forEachButLast(Iterator, Closure)} instead
     */
    @Deprecated
    public static <T, C extends Closure<? super T>> T forAllButLastDo(final Iterator<T> iterator, final C closure) {
        return closure != null ? IteratorUtils.forEachButLast(iterator, closure) : null;
    }

    /**
     * Filter the collection by applying a Predicate to each element. If the
     * predicate returns false, remove the element.
     * <p>
     * If the input collection or predicate is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Iterable} contains
     * @param collection  the collection to get the input from, may be null
     * @param predicate  the predicate to use as a filter, may be null
     * @return true if the collection is modified by this call, false otherwise.
     */
    public static <T> boolean filter(final Iterable<T> collection, final Predicate<? super T> predicate) {
        boolean result = false;
        if (collection != null && predicate != null) {
            for (final Iterator<T> it = collection.iterator(); it.hasNext();) {
                if (!predicate.evaluate(it.next())) {
                    it.remove();
                    result = true;
                }
            }
        }
        return result;
    }

    /**
     * Filter the collection by applying a Predicate to each element. If the
     * predicate returns true, remove the element.
     * <p>
     * This is equivalent to <pre>filter(collection, PredicateUtils.notPredicate(predicate))</pre>
     * if predicate is != null.
     * <p>
     * If the input collection or predicate is null, there is no change made.
     *
     * @param <T>  the type of object the {@link Iterable} contains
     * @param collection  the collection to get the input from, may be null
     * @param predicate  the predicate to use as a filter, may be null
     * @return true if the collection is modified by this call, false otherwise.
     */
    public static <T> boolean filterInverse(final Iterable<T> collection, final Predicate<? super T> predicate) {
        return filter(collection, predicate == null ? null : PredicateUtils.notPredicate(predicate));
    }

    /**
     * Transform the collection by applying a Transformer to each element.
     * <p>
     * If the input collection or transformer is null, there is no change made.
     * <p>
     * This routine is best for Lists, for which set() is used to do the
     * transformations "in place." For other Collections, clear() and addAll()
     * are used to replace elements.
     * <p>
     * If the input collection controls its input, such as a Set, and the
     * Transformer creates duplicates (or are otherwise invalid), the collection
     * may reduce in size due to calling this method.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the {@link Collection} to get the input from, may be null
     * @param transformer  the transformer to perform, may be null
     */
    public static <C> void transform(final Collection<C> collection,
                                     final Transformer<? super C, ? extends C> transformer) {

        if (collection != null && transformer != null) {
            if (collection instanceof List<?>) {
                final List<C> list = (List<C>) collection;
                for (final ListIterator<C> it = list.listIterator(); it.hasNext();) {
                    it.set(transformer.transform(it.next()));
                }
            } else {
                final Collection<C> resultCollection = collect(collection, transformer);
                collection.clear();
                collection.addAll(resultCollection);
            }
        }
    }

    /**
     * Counts the number of elements in the input collection that match the
     * predicate.
     * <p>
     * A <code>null</code> collection or predicate matches no elements.
     *
     * @param <C>  the type of object the {@link Iterable} contains
     * @param input  the {@link Iterable} to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @return the number of matches for the predicate in the collection
     * @deprecated since 4.1, use {@link IterableUtils#countMatches(Iterable, Predicate)} instead
     */
    @Deprecated
    public static <C> int countMatches(final Iterable<C> input, final Predicate<? super C> predicate) {
        return predicate == null ? 0 : (int) IterableUtils.countMatches(input, predicate);
    }

    /**
     * Answers true if a predicate is true for at least one element of a
     * collection.
     * <p>
     * A <code>null</code> collection or predicate returns false.
     *
     * @param <C>  the type of object the {@link Iterable} contains
     * @param input  the {@link Iterable} to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @return true if at least one element of the collection matches the predicate
     * @deprecated since 4.1, use {@link IterableUtils#matchesAny(Iterable, Predicate)} instead
     */
    @Deprecated
    public static <C> boolean exists(final Iterable<C> input, final Predicate<? super C> predicate) {
        return predicate != null && IterableUtils.matchesAny(input, predicate);
    }

    /**
     * Answers true if a predicate is true for every element of a
     * collection.
     * <p>
     * A <code>null</code> predicate returns false.<br>
     * A <code>null</code> or empty collection returns true.
     *
     * @param <C>  the type of object the {@link Iterable} contains
     * @param input  the {@link Iterable} to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @return true if every element of the collection matches the predicate or if the
     * collection is empty, false otherwise
     * @since 4.0
     * @deprecated since 4.1, use {@link IterableUtils#matchesAll(Iterable, Predicate)} instead
     */
    @Deprecated
    public static <C> boolean matchesAll(final Iterable<C> input, final Predicate<? super C> predicate) {
        return predicate != null && IterableUtils.matchesAll(input, predicate);
    }

    /**
     * Selects all elements from input collection which match the given
     * predicate into an output collection.
     * <p>
     * A <code>null</code> predicate matches no elements.
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param inputCollection  the collection to get the input from, may not be null
     * @param predicate  the predicate to use, may be null
     * @return the elements matching the predicate (new list)
     * @throws NullPointerException if the input collection is null
     */
    public static <O> Collection<O> select(final Iterable<? extends O> inputCollection,
                                           final Predicate<? super O> predicate) {
        final Collection<O> answer = inputCollection instanceof Collection<?> ?
                new ArrayList<O>(((Collection<?>) inputCollection).size()) : new ArrayList<O>();
        return select(inputCollection, predicate, answer);
    }

    /**
     * Selects all elements from input collection which match the given
     * predicate and adds them to outputCollection.
     * <p>
     * If the input collection or predicate is null, there is no change to the
     * output collection.
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param <R>  the type of the output {@link Collection}
     * @param inputCollection  the collection to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @param outputCollection  the collection to output into, may not be null if the inputCollection
     *   and predicate or not null
     * @return the outputCollection
     */
    public static <O, R extends Collection<? super O>> R select(final Iterable<? extends O> inputCollection,
            final Predicate<? super O> predicate, final R outputCollection) {

        if (inputCollection != null && predicate != null) {
            for (final O item : inputCollection) {
                if (predicate.evaluate(item)) {
                    outputCollection.add(item);
                }
            }
        }
        return outputCollection;
    }

    /**
     * Selects all elements from inputCollection into an output and rejected collection,
     * based on the evaluation of the given predicate.
     * <p>
     * Elements matching the predicate are added to the <code>outputCollection</code>,
     * all other elements are added to the <code>rejectedCollection</code>.
     * <p>
     * If the input predicate is <code>null</code>, no elements are added to
     * <code>outputCollection</code> or <code>rejectedCollection</code>.
     * <p>
     * Note: calling the method is equivalent to the following code snippet:
     * <pre>
     *   select(inputCollection, predicate, outputCollection);
     *   selectRejected(inputCollection, predicate, rejectedCollection);
     * </pre>
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param <R>  the type of the output {@link Collection}
     * @param inputCollection  the collection to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @param outputCollection  the collection to output selected elements into, may not be null if the
     *   inputCollection and predicate are not null
     * @param rejectedCollection  the collection to output rejected elements into, may not be null if the
     *   inputCollection or predicate are not null
     * @return the outputCollection
     * @since 4.1
     */
    public static <O, R extends Collection<? super O>> R select(final Iterable<? extends O> inputCollection,
            final Predicate<? super O> predicate, final R outputCollection, final R rejectedCollection) {

        if (inputCollection != null && predicate != null) {
            for (final O element : inputCollection) {
                if (predicate.evaluate(element)) {
                    outputCollection.add(element);
                } else {
                    rejectedCollection.add(element);
                }
            }
        }
        return outputCollection;
    }

    /**
     * Selects all elements from inputCollection which don't match the given
     * predicate into an output collection.
     * <p>
     * If the input predicate is <code>null</code>, the result is an empty
     * list.
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param inputCollection  the collection to get the input from, may not be null
     * @param predicate  the predicate to use, may be null
     * @return the elements <b>not</b> matching the predicate (new list)
     * @throws NullPointerException if the input collection is null
     */
    public static <O> Collection<O> selectRejected(final Iterable<? extends O> inputCollection,
                                                   final Predicate<? super O> predicate) {
        final Collection<O> answer = inputCollection instanceof Collection<?> ?
                new ArrayList<O>(((Collection<?>) inputCollection).size()) : new ArrayList<O>();
        return selectRejected(inputCollection, predicate, answer);
    }

    /**
     * Selects all elements from inputCollection which don't match the given
     * predicate and adds them to outputCollection.
     * <p>
     * If the input predicate is <code>null</code>, no elements are added to
     * <code>outputCollection</code>.
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param <R>  the type of the output {@link Collection}
     * @param inputCollection  the collection to get the input from, may be null
     * @param predicate  the predicate to use, may be null
     * @param outputCollection  the collection to output into, may not be null if the inputCollection
     *   and predicate or not null
     * @return outputCollection
     */
    public static <O, R extends Collection<? super O>> R selectRejected(final Iterable<? extends O> inputCollection,
            final Predicate<? super O> predicate, final R outputCollection) {

        if (inputCollection != null && predicate != null) {
            for (final O item : inputCollection) {
                if (!predicate.evaluate(item)) {
                    outputCollection.add(item);
                }
            }
        }
        return outputCollection;
    }

    /**
     * Returns a new Collection containing all elements of the input collection
     * transformed by the given transformer.
     * <p>
     * If the input collection or transformer is null, the result is an empty list.
     *
     * @param <I>  the type of object in the input collection
     * @param <O>  the type of object in the output collection
     * @param inputCollection  the collection to get the input from, may not be null
     * @param transformer  the transformer to use, may be null
     * @return the transformed result (new list)
     * @throws NullPointerException if the input collection is null
     */
    public static <I, O> Collection<O> collect(final Iterable<I> inputCollection,
                                               final Transformer<? super I, ? extends O> transformer) {
        final Collection<O> answer = inputCollection instanceof Collection<?> ?
                new ArrayList<O>(((Collection<?>) inputCollection).size()) : new ArrayList<O>();
        return collect(inputCollection, transformer, answer);
    }

    /**
     * Transforms all elements from the input iterator with the given transformer
     * and adds them to the output collection.
     * <p>
     * If the input iterator or transformer is null, the result is an empty list.
     *
     * @param <I>  the type of object in the input collection
     * @param <O>  the type of object in the output collection
     * @param inputIterator  the iterator to get the input from, may be null
     * @param transformer  the transformer to use, may be null
     * @return the transformed result (new list)
     */
    public static <I, O> Collection<O> collect(final Iterator<I> inputIterator,
                                               final Transformer<? super I, ? extends O> transformer) {
        return collect(inputIterator, transformer, new ArrayList<O>());
    }

    /**
     * Transforms all elements from input collection with the given transformer
     * and adds them to the output collection.
     * <p>
     * If the input collection or transformer is null, there is no change to the
     * output collection.
     *
     * @param <I>  the type of object in the input collection
     * @param <O>  the type of object in the output collection
     * @param <R>  the type of the output collection
     * @param inputCollection  the collection to get the input from, may be null
     * @param transformer  the transformer to use, may be null
     * @param outputCollection  the collection to output into, may not be null if inputCollection
     *   and transformer are not null
     * @return the output collection with the transformed input added
     * @throws NullPointerException if the outputCollection is null and both, inputCollection and
     *   transformer are not null
     */
    public static <I, O, R extends Collection<? super O>> R collect(final Iterable<? extends I> inputCollection,
            final Transformer<? super I, ? extends O> transformer, final R outputCollection) {
        if (inputCollection != null) {
            return collect(inputCollection.iterator(), transformer, outputCollection);
        }
        return outputCollection;
    }

    /**
     * Transforms all elements from the input iterator with the given transformer
     * and adds them to the output collection.
     * <p>
     * If the input iterator or transformer is null, there is no change to the
     * output collection.
     *
     * @param <I>  the type of object in the input collection
     * @param <O>  the type of object in the output collection
     * @param <R>  the type of the output collection
     * @param inputIterator  the iterator to get the input from, may be null
     * @param transformer  the transformer to use, may be null
     * @param outputCollection  the collection to output into, may not be null if inputIterator
     *   and transformer are not null
     * @return the outputCollection with the transformed input added
     * @throws NullPointerException if the output collection is null and both, inputIterator and
     *   transformer are not null
     */
    public static <I, O, R extends Collection<? super O>> R collect(final Iterator<? extends I> inputIterator,
            final Transformer<? super I, ? extends O> transformer, final R outputCollection) {
        if (inputIterator != null && transformer != null) {
            while (inputIterator.hasNext()) {
                final I item = inputIterator.next();
                final O value = transformer.transform(item);
                outputCollection.add(value);
            }
        }
        return outputCollection;
    }

    //-----------------------------------------------------------------------
    /**
     * Adds an element to the collection unless the element is null.
     *
     * @param <T>  the type of object the {@link Collection} contains
     * @param collection  the collection to add to, must not be null
     * @param object  the object to add, if null it will not be added
     * @return true if the collection changed
     * @throws NullPointerException if the collection is null
     * @since 3.2
     */
    public static <T> boolean addIgnoreNull(final Collection<T> collection, final T object) {
        if (collection == null) {
            throw new NullPointerException("The collection must not be null");
        }
        return object != null && collection.add(object);
    }

    /**
     * Adds all elements in the {@link Iterable} to the given collection. If the
     * {@link Iterable} is a {@link Collection} then it is cast and will be
     * added using {@link Collection#addAll(Collection)} instead of iterating.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to add to, must not be null
     * @param iterable  the iterable of elements to add, must not be null
     * @return a boolean indicating whether the collection has changed or not.
     * @throws NullPointerException if the collection or iterator is null
     */
    public static <C> boolean addAll(final Collection<C> collection, final Iterable<? extends C> iterable) {
        if (iterable instanceof Collection<?>) {
            return collection.addAll((Collection<? extends C>) iterable);
        }
        return addAll(collection, iterable.iterator());
    }

    /**
     * Adds all elements in the iteration to the given collection.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to add to, must not be null
     * @param iterator  the iterator of elements to add, must not be null
     * @return a boolean indicating whether the collection has changed or not.
     * @throws NullPointerException if the collection or iterator is null
     */
    public static <C> boolean addAll(final Collection<C> collection, final Iterator<? extends C> iterator) {
        boolean changed = false;
        while (iterator.hasNext()) {
            changed |= collection.add(iterator.next());
        }
        return changed;
    }

    /**
     * Adds all elements in the enumeration to the given collection.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to add to, must not be null
     * @param enumeration  the enumeration of elements to add, must not be null
     * @return {@code true} if the collections was changed, {@code false} otherwise
     * @throws NullPointerException if the collection or enumeration is null
     */
    public static <C> boolean addAll(final Collection<C> collection, final Enumeration<? extends C> enumeration) {
        boolean changed = false;
        while (enumeration.hasMoreElements()) {
            changed |= collection.add(enumeration.nextElement());
        }
        return changed;
    }

    /**
     * Adds all elements in the array to the given collection.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to add to, must not be null
     * @param elements  the array of elements to add, must not be null
     * @return {@code true} if the collection was changed, {@code false} otherwise
     * @throws NullPointerException if the collection or array is null
     */
    public static <C> boolean addAll(final Collection<C> collection, final C... elements) {
        boolean changed = false;
        for (final C element : elements) {
            changed |= collection.add(element);
        }
        return changed;
    }

    /**
     * Returns the <code>index</code>-th value in {@link Iterator}, throwing
     * <code>IndexOutOfBoundsException</code> if there is no such element.
     * <p>
     * The Iterator is advanced to <code>index</code> (or to the end, if
     * <code>index</code> exceeds the number of entries) as a side effect of this method.
     *
     * @param iterator  the iterator to get a value from
     * @param index  the index to get
     * @param <T> the type of object in the {@link Iterator}
     * @return the object at the specified index
     * @throws IndexOutOfBoundsException if the index is invalid
     * @throws IllegalArgumentException if the object type is invalid
     * @deprecated since 4.1, use {@code IteratorUtils.get(Iterator, int)} instead
     */
    @Deprecated
    public static <T> T get(final Iterator<T> iterator, final int index) {
        return IteratorUtils.get(iterator, index);
    }

    /**
     * Ensures an index is not negative.
     * @param index the index to check.
     * @throws IndexOutOfBoundsException if the index is negative.
     */
    static void checkIndexBounds(final int index) {
        if (index < 0) {
            throw new IndexOutOfBoundsException("Index cannot be negative: " + index);
        }
    }

    /**
     * Returns the <code>index</code>-th value in the <code>iterable</code>'s {@link Iterator}, throwing
     * <code>IndexOutOfBoundsException</code> if there is no such element.
     * <p>
     * If the {@link Iterable} is a {@link List}, then it will use {@link List#get(int)}.
     *
     * @param iterable  the {@link Iterable} to get a value from
     * @param index  the index to get
     * @param <T> the type of object in the {@link Iterable}.
     * @return the object at the specified index
     * @throws IndexOutOfBoundsException if the index is invalid
     * @deprecated since 4.1, use {@code IterableUtils.get(Iterable, int)} instead
     */
    @Deprecated
    public static <T> T get(final Iterable<T> iterable, final int index) {
        return IterableUtils.get(iterable, index);
    }

    /**
     * Returns the <code>index</code>-th value in <code>object</code>, throwing
     * <code>IndexOutOfBoundsException</code> if there is no such element or
     * <code>IllegalArgumentException</code> if <code>object</code> is not an
     * instance of one of the supported types.
     * <p>
     * The supported types, and associated semantics are:
     * <ul>
     * <li> Map -- the value returned is the <code>Map.Entry</code> in position
     *      <code>index</code> in the map's <code>entrySet</code> iterator,
     *      if there is such an entry.</li>
     * <li> List -- this method is equivalent to the list's get method.</li>
     * <li> Array -- the <code>index</code>-th array entry is returned,
     *      if there is such an entry; otherwise an <code>IndexOutOfBoundsException</code>
     *      is thrown.</li>
     * <li> Collection -- the value returned is the <code>index</code>-th object
     *      returned by the collection's default iterator, if there is such an element.</li>
     * <li> Iterator or Enumeration -- the value returned is the
     *      <code>index</code>-th object in the Iterator/Enumeration, if there
     *      is such an element.  The Iterator/Enumeration is advanced to
     *      <code>index</code> (or to the end, if <code>index</code> exceeds the
     *      number of entries) as a side effect of this method.</li>
     * </ul>
     *
     * @param object  the object to get a value from
     * @param index  the index to get
     * @return the object at the specified index
     * @throws IndexOutOfBoundsException if the index is invalid
     * @throws IllegalArgumentException if the object type is invalid
     */
    public static Object get(final Object object, final int index) {
        final int i = index;
        if (i < 0) {
            throw new IndexOutOfBoundsException("Index cannot be negative: " + i);
        }
        if (object instanceof Map<?,?>) {
            final Map<?, ?> map = (Map<?, ?>) object;
            final Iterator<?> iterator = map.entrySet().iterator();
            return IteratorUtils.get(iterator, i);
        } else if (object instanceof Object[]) {
            return ((Object[]) object)[i];
        } else if (object instanceof Iterator<?>) {
            final Iterator<?> it = (Iterator<?>) object;
            return IteratorUtils.get(it, i);
        } else if (object instanceof Iterable<?>) {
            final Iterable<?> iterable = (Iterable<?>) object;
            return IterableUtils.get(iterable, i);
        } else if (object instanceof Enumeration<?>) {
            final Enumeration<?> it = (Enumeration<?>) object;
            return EnumerationUtils.get(it, i);
        } else if (object == null) {
            throw new IllegalArgumentException("Unsupported object type: null");
        } else {
            try {
                return Array.get(object, i);
            } catch (final IllegalArgumentException ex) {
                throw new IllegalArgumentException("Unsupported object type: " + object.getClass().getName());
            }
        }
    }

    /**
     * Returns the <code>index</code>-th <code>Map.Entry</code> in the <code>map</code>'s <code>entrySet</code>,
     * throwing <code>IndexOutOfBoundsException</code> if there is no such element.
     *
     * @param <K>  the key type in the {@link Map}
     * @param <V>  the key type in the {@link Map}
     * @param map  the object to get a value from
     * @param index  the index to get
     * @return the object at the specified index
     * @throws IndexOutOfBoundsException if the index is invalid
     */
    public static <K,V> Map.Entry<K, V> get(final Map<K,V> map, final int index) {
        checkIndexBounds(index);
        return get(map.entrySet(), index);
    }

    /**
     * Gets the size of the collection/iterator specified.
     * <p>
     * This method can handles objects as follows
     * <ul>
     * <li>Collection - the collection size
     * <li>Map - the map size
     * <li>Array - the array size
     * <li>Iterator - the number of elements remaining in the iterator
     * <li>Enumeration - the number of elements remaining in the enumeration
     * </ul>
     *
     * @param object  the object to get the size of, may be null
     * @return the size of the specified collection or 0 if the object was null
     * @throws IllegalArgumentException thrown if object is not recognized
     * @since 3.1
     */
    public static int size(final Object object) {
        if (object == null) {
            return 0;
        }
        int total = 0;
        if (object instanceof Map<?,?>) {
            total = ((Map<?, ?>) object).size();
        } else if (object instanceof Collection<?>) {
            total = ((Collection<?>) object).size();
        } else if (object instanceof Iterable<?>) {
            total = IterableUtils.size((Iterable<?>) object);
        } else if (object instanceof Object[]) {
            total = ((Object[]) object).length;
        } else if (object instanceof Iterator<?>) {
            total = IteratorUtils.size((Iterator<?>) object);
        } else if (object instanceof Enumeration<?>) {
            final Enumeration<?> it = (Enumeration<?>) object;
            while (it.hasMoreElements()) {
                total++;
                it.nextElement();
            }
        } else {
            try {
                total = Array.getLength(object);
            } catch (final IllegalArgumentException ex) {
                throw new IllegalArgumentException("Unsupported object type: " + object.getClass().getName());
            }
        }
        return total;
    }

    /**
     * Checks if the specified collection/array/iterator is empty.
     * <p>
     * This method can handles objects as follows
     * <ul>
     * <li>Collection - via collection isEmpty
     * <li>Map - via map isEmpty
     * <li>Array - using array size
     * <li>Iterator - via hasNext
     * <li>Enumeration - via hasMoreElements
     * </ul>
     * <p>
     * Note: This method is named to avoid clashing with
     * {@link #isEmpty(Collection)}.
     *
     * @param object  the object to get the size of, may be null
     * @return true if empty or null
     * @throws IllegalArgumentException thrown if object is not recognized
     * @since 3.2
     */
    public static boolean sizeIsEmpty(final Object object) {
        if (object == null) {
            return true;
        } else if (object instanceof Collection<?>) {
            return ((Collection<?>) object).isEmpty();
        } else if (object instanceof Iterable<?>) {
            return IterableUtils.isEmpty((Iterable<?>) object);
        } else if (object instanceof Map<?, ?>) {
            return ((Map<?, ?>) object).isEmpty();
        } else if (object instanceof Object[]) {
            return ((Object[]) object).length == 0;
        } else if (object instanceof Iterator<?>) {
            return ((Iterator<?>) object).hasNext() == false;
        } else if (object instanceof Enumeration<?>) {
            return ((Enumeration<?>) object).hasMoreElements() == false;
        } else {
            try {
                return Array.getLength(object) == 0;
            } catch (final IllegalArgumentException ex) {
                throw new IllegalArgumentException("Unsupported object type: " + object.getClass().getName());
            }
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Null-safe check if the specified collection is empty.
     * <p>
     * Null returns true.
     *
     * @param coll  the collection to check, may be null
     * @return true if empty or null
     * @since 3.2
     */
    public static boolean isEmpty(final Collection<?> coll) {
        return coll == null || coll.isEmpty();
    }

    /**
     * Null-safe check if the specified collection is not empty.
     * <p>
     * Null returns false.
     *
     * @param coll  the collection to check, may be null
     * @return true if non-null and non-empty
     * @since 3.2
     */
    public static boolean isNotEmpty(final Collection<?> coll) {
        return !isEmpty(coll);
    }

    //-----------------------------------------------------------------------
    /**
     * Reverses the order of the given array.
     *
     * @param array  the array to reverse
     */
    public static void reverseArray(final Object[] array) {
        int i = 0;
        int j = array.length - 1;
        Object tmp;

        while (j > i) {
            tmp = array[j];
            array[j] = array[i];
            array[i] = tmp;
            j--;
            i++;
        }
    }

    /**
     * Returns true if no more elements can be added to the Collection.
     * <p>
     * This method uses the {@link BoundedCollection} interface to determine the
     * full status. If the collection does not implement this interface then
     * false is returned.
     * <p>
     * The collection does not have to implement this interface directly.
     * If the collection has been decorated using the decorators subpackage
     * then these will be removed to access the BoundedCollection.
     *
     * @param coll  the collection to check
     * @return true if the BoundedCollection is full
     * @throws NullPointerException if the collection is null
     */
    public static boolean isFull(final Collection<? extends Object> coll) {
        if (coll == null) {
            throw new NullPointerException("The collection must not be null");
        }
        if (coll instanceof BoundedCollection) {
            return ((BoundedCollection<?>) coll).isFull();
        }
        try {
            final BoundedCollection<?> bcoll =
                    UnmodifiableBoundedCollection.unmodifiableBoundedCollection(coll);
            return bcoll.isFull();
        } catch (final IllegalArgumentException ex) {
            return false;
        }
    }

    /**
     * Get the maximum number of elements that the Collection can contain.
     * <p>
     * This method uses the {@link BoundedCollection} interface to determine the
     * maximum size. If the collection does not implement this interface then
     * -1 is returned.
     * <p>
     * The collection does not have to implement this interface directly.
     * If the collection has been decorated using the decorators subpackage
     * then these will be removed to access the BoundedCollection.
     *
     * @param coll  the collection to check
     * @return the maximum size of the BoundedCollection, -1 if no maximum size
     * @throws NullPointerException if the collection is null
     */
    public static int maxSize(final Collection<? extends Object> coll) {
        if (coll == null) {
            throw new NullPointerException("The collection must not be null");
        }
        if (coll instanceof BoundedCollection) {
            return ((BoundedCollection<?>) coll).maxSize();
        }
        try {
            final BoundedCollection<?> bcoll =
                    UnmodifiableBoundedCollection.unmodifiableBoundedCollection(coll);
            return bcoll.maxSize();
        } catch (final IllegalArgumentException ex) {
            return -1;
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Merges two sorted Collections, a and b, into a single, sorted List
     * such that the natural ordering of the elements is retained.
     * <p>
     * Uses the standard O(n) merge algorithm for combining two sorted lists.
     *
     * @param <O>  the element type
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @return a new sorted List, containing the elements of Collection a and b
     * @throws NullPointerException if either collection is null
     * @since 4.0
     */
    public static <O extends Comparable<? super O>> List<O> collate(final Iterable<? extends O> a,
                                                                    final Iterable<? extends O> b) {
        return collate(a, b, ComparatorUtils.<O>naturalComparator(), true);
    }

    /**
     * Merges two sorted Collections, a and b, into a single, sorted List
     * such that the natural ordering of the elements is retained.
     * <p>
     * Uses the standard O(n) merge algorithm for combining two sorted lists.
     *
     * @param <O>  the element type
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @param includeDuplicates  if {@code true} duplicate elements will be retained, otherwise
     *   they will be removed in the output collection
     * @return a new sorted List, containing the elements of Collection a and b
     * @throws NullPointerException if either collection is null
     * @since 4.0
     */
    public static <O extends Comparable<? super O>> List<O> collate(final Iterable<? extends O> a,
                                                                    final Iterable<? extends O> b,
                                                                    final boolean includeDuplicates) {
        return collate(a, b, ComparatorUtils.<O>naturalComparator(), includeDuplicates);
    }

    /**
     * Merges two sorted Collections, a and b, into a single, sorted List
     * such that the ordering of the elements according to Comparator c is retained.
     * <p>
     * Uses the standard O(n) merge algorithm for combining two sorted lists.
     *
     * @param <O>  the element type
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @param c  the comparator to use for the merge.
     * @return a new sorted List, containing the elements of Collection a and b
     * @throws NullPointerException if either collection or the comparator is null
     * @since 4.0
     */
    public static <O> List<O> collate(final Iterable<? extends O> a, final Iterable<? extends O> b,
                                      final Comparator<? super O> c) {
        return collate(a, b, c, true);
    }

    /**
     * Merges two sorted Collections, a and b, into a single, sorted List
     * such that the ordering of the elements according to Comparator c is retained.
     * <p>
     * Uses the standard O(n) merge algorithm for combining two sorted lists.
     *
     * @param <O>  the element type
     * @param a  the first collection, must not be null
     * @param b  the second collection, must not be null
     * @param c  the comparator to use for the merge.
     * @param includeDuplicates  if {@code true} duplicate elements will be retained, otherwise
     *   they will be removed in the output collection
     * @return a new sorted List, containing the elements of Collection a and b
     * @throws NullPointerException if either collection or the comparator is null
     * @since 4.0
     */
    public static <O> List<O> collate(final Iterable<? extends O> a, final Iterable<? extends O> b,
                                      final Comparator<? super O> c, final boolean includeDuplicates) {

        if (a == null || b == null) {
            throw new NullPointerException("The collections must not be null");
        }
        if (c == null) {
            throw new NullPointerException("The comparator must not be null");
        }

        // if both Iterables are a Collection, we can estimate the size
        final int totalSize = a instanceof Collection<?> && b instanceof Collection<?> ?
                Math.max(1, ((Collection<?>) a).size() + ((Collection<?>) b).size()) : 10;

        final Iterator<O> iterator = new CollatingIterator<>(c, a.iterator(), b.iterator());
        if (includeDuplicates) {
            return IteratorUtils.toList(iterator, totalSize);
        }
        final ArrayList<O> mergedList = new ArrayList<>(totalSize);

        O lastItem = null;
        while (iterator.hasNext()) {
            final O item = iterator.next();
            if (lastItem == null || !lastItem.equals(item)) {
                mergedList.add(item);
            }
            lastItem = item;
        }

        mergedList.trimToSize();
        return mergedList;
    }

    //-----------------------------------------------------------------------

    /**
     * Returns a {@link Collection} of all the permutations of the input collection.
     * <p>
     * NOTE: the number of permutations of a given collection is equal to n!, where
     * n is the size of the collection. Thus, the resulting collection will become
     * <b>very</b> large for collections &gt; 10 (e.g. 10! = 3628800, 15! = 1307674368000).
     * <p>
     * For larger collections it is advised to use a {@link PermutationIterator} to
     * iterate over all permutations.
     *
     * @see PermutationIterator
     *
     * @param <E>  the element type
     * @param collection  the collection to create permutations for, may not be null
     * @return an unordered collection of all permutations of the input collection
     * @throws NullPointerException if collection is null
     * @since 4.0
     */
    public static <E> Collection<List<E>> permutations(final Collection<E> collection) {
        final PermutationIterator<E> it = new PermutationIterator<>(collection);
        final Collection<List<E>> result = new ArrayList<>();
        while (it.hasNext()) {
            result.add(it.next());
        }
        return result;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns a collection containing all the elements in <code>collection</code>
     * that are also in <code>retain</code>. The cardinality of an element <code>e</code>
     * in the returned collection is the same as the cardinality of <code>e</code>
     * in <code>collection</code> unless <code>retain</code> does not contain <code>e</code>, in which
     * case the cardinality is zero. This method is useful if you do not wish to modify
     * the collection <code>c</code> and thus cannot call <code>c.retainAll(retain);</code>.
     * <p>
     * This implementation iterates over <code>collection</code>, checking each element in
     * turn to see if it's contained in <code>retain</code>. If it's contained, it's added
     * to the returned list. As a consequence, it is advised to use a collection type for
     * <code>retain</code> that provides a fast (e.g. O(1)) implementation of
     * {@link Collection#contains(Object)}.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection whose contents are the target of the #retailAll operation
     * @param retain  the collection containing the elements to be retained in the returned collection
     * @return a <code>Collection</code> containing all the elements of <code>collection</code>
     * that occur at least once in <code>retain</code>.
     * @throws NullPointerException if either parameter is null
     * @since 3.2
     */
    public static <C> Collection<C> retainAll(final Collection<C> collection, final Collection<?> retain) {
        return ListUtils.retainAll(collection, retain);
    }

    /**
     * Returns a collection containing all the elements in
     * <code>collection</code> that are also in <code>retain</code>. The
     * cardinality of an element <code>e</code> in the returned collection is
     * the same as the cardinality of <code>e</code> in <code>collection</code>
     * unless <code>retain</code> does not contain <code>e</code>, in which case
     * the cardinality is zero. This method is useful if you do not wish to
     * modify the collection <code>c</code> and thus cannot call
     * <code>c.retainAll(retain);</code>.
     * <p>
     * Moreover this method uses an {@link Equator} instead of
     * {@link Object#equals(Object)} to determine the equality of the elements
     * in <code>collection</code> and <code>retain</code>. Hence this method is
     * useful in cases where the equals behavior of an object needs to be
     * modified without changing the object itself.
     *
     * @param <E> the type of object the {@link Collection} contains
     * @param collection the collection whose contents are the target of the {@code retainAll} operation
     * @param retain the collection containing the elements to be retained in the returned collection
     * @param equator the Equator used for testing equality
     * @return a <code>Collection</code> containing all the elements of <code>collection</code>
     * that occur at least once in <code>retain</code> according to the <code>equator</code>
     * @throws NullPointerException if any of the parameters is null
     * @since 4.1
     */
    public static <E> Collection<E> retainAll(final Iterable<E> collection,
                                              final Iterable<? extends E> retain,
                                              final Equator<? super E> equator) {

        final Transformer<E, EquatorWrapper<E>> transformer = new Transformer<E, EquatorWrapper<E>>() {
            @Override
            public EquatorWrapper<E> transform(final E input) {
                return new EquatorWrapper<>(equator, input);
            }
        };

        final Set<EquatorWrapper<E>> retainSet =
                collect(retain, transformer, new HashSet<EquatorWrapper<E>>());

        final List<E> list = new ArrayList<>();
        for (final E element : collection) {
            if (retainSet.contains(new EquatorWrapper<>(equator, element))) {
                list.add(element);
            }
        }
        return list;
    }

    /**
     * Removes the elements in <code>remove</code> from <code>collection</code>. That is, this
     * method returns a collection containing all the elements in <code>c</code>
     * that are not in <code>remove</code>. The cardinality of an element <code>e</code>
     * in the returned collection is the same as the cardinality of <code>e</code>
     * in <code>collection</code> unless <code>remove</code> contains <code>e</code>, in which
     * case the cardinality is zero. This method is useful if you do not wish to modify
     * the collection <code>c</code> and thus cannot call <code>collection.removeAll(remove);</code>.
     * <p>
     * This implementation iterates over <code>collection</code>, checking each element in
     * turn to see if it's contained in <code>remove</code>. If it's not contained, it's added
     * to the returned list. As a consequence, it is advised to use a collection type for
     * <code>remove</code> that provides a fast (e.g. O(1)) implementation of
     * {@link Collection#contains(Object)}.
     *
     * @param <E>  the type of object the {@link Collection} contains
     * @param collection  the collection from which items are removed (in the returned collection)
     * @param remove  the items to be removed from the returned <code>collection</code>
     * @return a <code>Collection</code> containing all the elements of <code>collection</code> except
     * any elements that also occur in <code>remove</code>.
     * @throws NullPointerException if either parameter is null
     * @since 4.0 (method existed in 3.2 but was completely broken)
     */
    public static <E> Collection<E> removeAll(final Collection<E> collection, final Collection<?> remove) {
        return ListUtils.removeAll(collection, remove);
  }

    /**
     * Removes all elements in <code>remove</code> from <code>collection</code>.
     * That is, this method returns a collection containing all the elements in
     * <code>collection</code> that are not in <code>remove</code>. The
     * cardinality of an element <code>e</code> in the returned collection is
     * the same as the cardinality of <code>e</code> in <code>collection</code>
     * unless <code>remove</code> contains <code>e</code>, in which case the
     * cardinality is zero. This method is useful if you do not wish to modify
     * the collection <code>c</code> and thus cannot call
     * <code>collection.removeAll(remove)</code>.
     * <p>
     * Moreover this method uses an {@link Equator} instead of
     * {@link Object#equals(Object)} to determine the equality of the elements
     * in <code>collection</code> and <code>remove</code>. Hence this method is
     * useful in cases where the equals behavior of an object needs to be
     * modified without changing the object itself.
     *
     * @param <E> the type of object the {@link Collection} contains
     * @param collection the collection from which items are removed (in the returned collection)
     * @param remove the items to be removed from the returned collection
     * @param equator the Equator used for testing equality
     * @return a <code>Collection</code> containing all the elements of <code>collection</code>
     * except any element that if equal according to the <code>equator</code>
     * @throws NullPointerException if any of the parameters is null
     * @since 4.1
     */
    public static <E> Collection<E> removeAll(final Iterable<E> collection,
                                              final Iterable<? extends E> remove,
                                              final Equator<? super E> equator) {

        final Transformer<E, EquatorWrapper<E>> transformer = new Transformer<E, EquatorWrapper<E>>() {
            @Override
            public EquatorWrapper<E> transform(final E input) {
                return new EquatorWrapper<>(equator, input);
            }
        };

        final Set<EquatorWrapper<E>> removeSet =
                collect(remove, transformer, new HashSet<EquatorWrapper<E>>());

        final List<E> list = new ArrayList<>();
        for (final E element : collection) {
            if (!removeSet.contains(new EquatorWrapper<>(equator, element))) {
                list.add(element);
            }
        }
        return list;
    }

    //-----------------------------------------------------------------------
    /**
     * Returns a synchronized collection backed by the given collection.
     * <p>
     * You must manually synchronize on the returned buffer's iterator to
     * avoid non-deterministic behavior:
     *
     * <pre>
     * Collection c = CollectionUtils.synchronizedCollection(myCollection);
     * synchronized (c) {
     *     Iterator i = c.iterator();
     *     while (i.hasNext()) {
     *         process (i.next());
     *     }
     * }
     * </pre>
     *
     * This method uses the implementation in the decorators subpackage.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to synchronize, must not be null
     * @return a synchronized collection backed by the given collection
     * @throws NullPointerException if the collection is null
     * @deprecated since 4.1, use {@link java.util.Collections#synchronizedCollection(Collection)} instead
     */
    @Deprecated
    public static <C> Collection<C> synchronizedCollection(final Collection<C> collection) {
        return SynchronizedCollection.synchronizedCollection(collection);
    }

    /**
     * Returns an unmodifiable collection backed by the given collection.
     * <p>
     * This method uses the implementation in the decorators subpackage.
     *
     * @param <C>  the type of object the {@link Collection} contains
     * @param collection  the collection to make unmodifiable, must not be null
     * @return an unmodifiable collection backed by the given collection
     * @throws NullPointerException if the collection is null
     * @deprecated since 4.1, use {@link java.util.Collections#unmodifiableCollection(Collection)} instead
     */
    @Deprecated
    public static <C> Collection<C> unmodifiableCollection(final Collection<? extends C> collection) {
        return UnmodifiableCollection.unmodifiableCollection(collection);
    }

    /**
     * Returns a predicated (validating) collection backed by the given collection.
     * <p>
     * Only objects that pass the test in the given predicate can be added to the collection.
     * Trying to add an invalid object results in an IllegalArgumentException.
     * It is important not to use the original collection after invoking this method,
     * as it is a backdoor for adding invalid objects.
     *
     * @param <C> the type of objects in the Collection.
     * @param collection  the collection to predicate, must not be null
     * @param predicate  the predicate for the collection, must not be null
     * @return a predicated collection backed by the given collection
     * @throws NullPointerException if the Collection is null
     */
    public static <C> Collection<C> predicatedCollection(final Collection<C> collection,
                                                         final Predicate<? super C> predicate) {
        return PredicatedCollection.predicatedCollection(collection, predicate);
    }

    /**
     * Returns a transformed bag backed by the given collection.
     * <p>
     * Each object is passed through the transformer as it is added to the
     * Collection. It is important not to use the original collection after invoking this
     * method, as it is a backdoor for adding untransformed objects.
     * <p>
     * Existing entries in the specified collection will not be transformed.
     * If you want that behaviour, see {@link TransformedCollection#transformedCollection}.
     *
     * @param <E> the type of object the {@link Collection} contains
     * @param collection  the collection to predicate, must not be null
     * @param transformer  the transformer for the collection, must not be null
     * @return a transformed collection backed by the given collection
     * @throws NullPointerException if the Collection or Transformer is null
     */
    public static <E> Collection<E> transformingCollection(final Collection<E> collection,
            final Transformer<? super E, ? extends E> transformer) {
        return TransformedCollection.transformingCollection(collection, transformer);
    }

    /**
     * Extract the lone element of the specified Collection.
     * @param <E> collection type
     * @param collection to read
     * @return sole member of collection
     * @throws NullPointerException if collection is null
     * @throws IllegalArgumentException if collection is empty or contains more than one element
     * @since 4.0
     */
    public static <E> E extractSingleton(final Collection<E> collection) {
        if (collection == null) {
            throw new NullPointerException("Collection must not be null.");
        }
        if (collection.size() != 1) {
            throw new IllegalArgumentException("Can extract singleton only when collection size == 1");
        }
        return collection.iterator().next();
    }
}
