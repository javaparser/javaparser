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

import java.util.AbstractSet;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.IdentityHashMap;
import java.util.Iterator;
import java.util.NavigableSet;
import java.util.Set;
import java.util.SortedSet;
import java.util.TreeSet;

import org.apache.commons.collections4.set.ListOrderedSet;
import org.apache.commons.collections4.set.PredicatedNavigableSet;
import org.apache.commons.collections4.set.PredicatedSet;
import org.apache.commons.collections4.set.PredicatedSortedSet;
import org.apache.commons.collections4.set.TransformedNavigableSet;
import org.apache.commons.collections4.set.TransformedSet;
import org.apache.commons.collections4.set.TransformedSortedSet;
import org.apache.commons.collections4.set.UnmodifiableNavigableSet;
import org.apache.commons.collections4.set.UnmodifiableSet;
import org.apache.commons.collections4.set.UnmodifiableSortedSet;

/**
 * Provides utility methods and decorators for
 * {@link Set} and {@link SortedSet} instances.
 *
 * @since 2.1
 */
public class SetUtils {

    /**
     * An unmodifiable <b>view</b> of a set that may be backed by other sets.
     * <p>
     * If the decorated sets change, this view will change as well. The contents
     * of this view can be transferred to another instance via the {@link #copyInto(Set)}
     * and {@link #toSet()} methods.
     *
     * @param <E> the element type
     * @since 4.1
     */
    public static abstract class SetView<E> extends AbstractSet<E> {

        /**
         * Copies the contents of this view into the provided set.
         *
         * @param <S> the set type
         * @param set  the set for copying the contents
         */
        public <S extends Set<E>> void copyInto(final S set) {
            CollectionUtils.addAll(set, this);
        }

        /**
         * Return an iterator for this view; the returned iterator is
         * not required to be unmodifiable.
         * @return a new iterator for this view
         */
        protected abstract Iterator<E> createIterator();

        @Override
        public Iterator<E> iterator() {
            return IteratorUtils.unmodifiableIterator(createIterator());
        }

        @Override
        public int size() {
            return IteratorUtils.size(iterator());
        }

        /**
         * Returns a new set containing the contents of this view.
         *
         * @return a new set containing all elements of this view
         */
        public Set<E> toSet() {
            final Set<E> set = new HashSet<>(size());
            copyInto(set);
            return set;
        }
    }
    
    /**
     * An empty unmodifiable sorted set.
     * This is not provided in the JDK.
     */
    @SuppressWarnings("rawtypes")
    public static final SortedSet EMPTY_SORTED_SET =
            UnmodifiableSortedSet.unmodifiableSortedSet(new TreeSet<>());

    /**
     * Returns a unmodifiable <b>view</b> containing the difference of the given
     * {@link Set}s, denoted by {@code a \ b} (or {@code a - b}).
     * <p>
     * The returned view contains all elements of {@code a} that are not a member
     * of {@code b}.
     *
     * @param <E> the generic type that is able to represent the types contained
     *   in both input sets.
     * @param a  the set to subtract from, must not be null
     * @param b  the set to subtract, must not be null
     * @return a view of the relative complement of  of the two sets
     * @since 4.1
     */
    public static <E> SetView<E> difference(final Set<? extends E> a, final Set<? extends E> b) {
        if (a == null || b == null) {
            throw new NullPointerException("Sets must not be null.");
        }

        final Predicate<E> notContainedInB = new Predicate<E>() {
            @Override
            public boolean evaluate(final E object) {
                return !b.contains(object);
            }
        };

        return new SetView<E>() {
            @Override
            public boolean contains(final Object o) {
                return a.contains(o) && !b.contains(o);
            }

            @Override
            public Iterator<E> createIterator() {
                return IteratorUtils.filteredIterator(a.iterator(), notContainedInB);
            }
        };
    }

    /**
     * Returns a unmodifiable <b>view</b> of the symmetric difference of the given
     * {@link Set}s.
     * <p>
     * The returned view contains all elements of {@code a} and {@code b} that are
     * not a member of the other set.
     * <p>
     * This is equivalent to {@code union(difference(a, b), difference(b, a))}.
     *
     * @param <E> the generic type that is able to represent the types contained
     *   in both input sets.
     * @param a  the first set, must not be null
     * @param b  the second set, must not be null
     * @return a view of the symmetric difference of the two sets
     * @since 4.1
     */
    public static <E> SetView<E> disjunction(final Set<? extends E> a, final Set<? extends E> b) {
        if (a == null || b == null) {
            throw new NullPointerException("Sets must not be null.");
        }

        final SetView<E> aMinusB = difference(a, b);
        final SetView<E> bMinusA = difference(b, a);

        return new SetView<E>() {
            @Override
            public boolean contains(final Object o) {
                return a.contains(o) ^ b.contains(o);
            }

            @Override
            public Iterator<E> createIterator() {
                return IteratorUtils.chainedIterator(aMinusB.iterator(), bMinusA.iterator());
            }

            @Override
            public boolean isEmpty() {
                return aMinusB.isEmpty() && bMinusA.isEmpty();
            }

            @Override
            public int size() {
                return aMinusB.size() + bMinusA.size();
            }
        };
    }

    /**
     * Returns an immutable empty set if the argument is <code>null</code>,
     * or the argument itself otherwise.
     *
     * @param <T> the element type
     * @param set the set, possibly <code>null</code>
     * @return an empty set if the argument is <code>null</code>
     */
    public static <T> Set<T> emptyIfNull(final Set<T> set) {
        return set == null ? Collections.<T>emptySet() : set;
    }

    //-----------------------------------------------------------------------

    /**
     * Get a typed empty unmodifiable Set.
     * @param <E> the element type
     * @return an empty Set
     */
    public static <E> Set<E> emptySet() {
        return Collections.<E>emptySet();
    }

    /**
     * Get a typed empty unmodifiable sorted set.
     * @param <E> the element type
     * @return an empty sorted Set
     */
    @SuppressWarnings("unchecked") // empty set is OK for any type
    public static <E> SortedSet<E> emptySortedSet() {
        return EMPTY_SORTED_SET;
    }

    /**
     * Generates a hash code using the algorithm specified in
     * {@link java.util.Set#hashCode()}.
     * <p>
     * This method is useful for implementing <code>Set</code> when you cannot
     * extend AbstractSet. The method takes Collection instances to enable other
     * collection types to use the Set implementation algorithm.
     *
     * @param <T> the element type
     * @see java.util.Set#hashCode()
     * @param set  the set to calculate the hash code for, may be null
     * @return the hash code
     */
    public static <T> int hashCodeForSet(final Collection<T> set) {
        if (set == null) {
            return 0;
        }

        int hashCode = 0;
        for (final T obj : set) {
            if (obj != null) {
                hashCode += obj.hashCode();
            }
        }
        return hashCode;
    }

    /**
     * Create a set from the given items. If the passed var-args argument is {@code
     * null}, then the method returns {@code null}.
     * @param <E> the element type
     * @param items the elements that make up the new set
     * @return a set
     * @since 4.3
     */
    public static <E> HashSet<E> hashSet(final E... items) {
        if (items == null) {
            return null;
        }
        return new HashSet<>(Arrays.asList(items));
    }

    /**
     * Returns a unmodifiable <b>view</b> of the intersection of the given {@link Set}s.
     * <p>
     * The returned view contains all elements that are members of both input sets
     * ({@code a} and {@code b}).
     *
     * @param <E> the generic type that is able to represent the types contained
     *   in both input sets.
     * @param a  the first set, must not be null
     * @param b  the second set, must not be null
     * @return a view of the intersection of the two sets
     * @since 4.1
     */
    public static <E> SetView<E> intersection(final Set<? extends E> a, final Set<? extends E> b) {
        if (a == null || b == null) {
            throw new NullPointerException("Sets must not be null.");
        }

        final Predicate<E> containedInB = new Predicate<E>() {
            @Override
            public boolean evaluate(final E object) {
                return b.contains(object);
            }
        };

        return new SetView<E>() {
            @Override
            public boolean contains(final Object o) {
                return a.contains(o) && b.contains(o);
            }

            @Override
            public Iterator<E> createIterator() {
                return IteratorUtils.filteredIterator(a.iterator(), containedInB);
            }
        };
    }

    /**
     * Tests two sets for equality as per the <code>equals()</code> contract
     * in {@link java.util.Set#equals(java.lang.Object)}.
     * <p>
     * This method is useful for implementing <code>Set</code> when you cannot
     * extend AbstractSet. The method takes Collection instances to enable other
     * collection types to use the Set implementation algorithm.
     * <p>
     * The relevant text (slightly paraphrased as this is a static method) is:
     * <blockquote>
     * <p>Two sets are considered equal if they have
     * the same size, and every member of the first set is contained in
     * the second. This ensures that the {@code equals} method works
     * properly across different implementations of the {@code Set}
     * interface.</p>
     *
     * <p>
     * This implementation first checks if the two sets are the same object:
     * if so it returns {@code true}.  Then, it checks if the two sets are
     * identical in size; if not, it returns false. If so, it returns
     * {@code a.containsAll((Collection) b)}.</p>
     * </blockquote>
     *
     * @see java.util.Set
     * @param set1  the first set, may be null
     * @param set2  the second set, may be null
     * @return whether the sets are equal by value comparison
     */
    public static boolean isEqualSet(final Collection<?> set1, final Collection<?> set2) {
        if (set1 == set2) {
            return true;
        }
        if (set1 == null || set2 == null || set1.size() != set2.size()) {
            return false;
        }

        return set1.containsAll(set2);
    }

    /**
     * Returns a new hash set that matches elements based on <code>==</code> not
     * <code>equals()</code>.
     * <p>
     * <strong>This set will violate the detail of various Set contracts.</strong>
     * As a general rule, don't compare this set to other sets. In particular, you can't
     * use decorators like {@link ListOrderedSet} on it, which silently assume that these
     * contracts are fulfilled.
     * <p>
     * <strong>Note that the returned set is not synchronized and is not thread-safe.</strong>
     * If you wish to use this set from multiple threads concurrently, you must use
     * appropriate synchronization. The simplest approach is to wrap this map
     * using {@link java.util.Collections#synchronizedSet(Set)}. This class may throw
     * exceptions when accessed by concurrent threads without synchronization.
     *
     * @param <E>  the element type
     * @return a new identity hash set
     * @since 4.1
     */
    public static <E> Set<E> newIdentityHashSet() {
        return Collections.newSetFromMap(new IdentityHashMap<E, Boolean>());
    }

    /**
     * Returns a set that maintains the order of elements that are added
     * backed by the given set.
     * <p>
     * If an element is added twice, the order is determined by the first add.
     * The order is observed through the iterator or toArray.
     *
     * @param <E> the element type
     * @param set  the set to order, must not be null
     * @return an ordered set backed by the given set
     * @throws NullPointerException if the set is null
     */
    public static <E> Set<E> orderedSet(final Set<E> set) {
        return ListOrderedSet.listOrderedSet(set);
    }

    /**
     * Returns a predicated (validating) navigable set backed by the given navigable set.
     * <p>
     * Only objects that pass the test in the given predicate can be added to the set.
     * Trying to add an invalid object results in an IllegalArgumentException.
     * It is important not to use the original set after invoking this method,
     * as it is a backdoor for adding invalid objects.
     *
     * @param <E> the element type
     * @param set  the navigable set to predicate, must not be null
     * @param predicate  the predicate for the navigable set, must not be null
     * @return a predicated navigable set backed by the given navigable set
     * @throws NullPointerException if the set or predicate is null
     * @since 4.1
     */
    public static <E> SortedSet<E> predicatedNavigableSet(final NavigableSet<E> set,
                                                          final Predicate<? super E> predicate) {
        return PredicatedNavigableSet.predicatedNavigableSet(set, predicate);
    }

    /**
     * Returns a predicated (validating) set backed by the given set.
     * <p>
     * Only objects that pass the test in the given predicate can be added to the set.
     * Trying to add an invalid object results in an IllegalArgumentException.
     * It is important not to use the original set after invoking this method,
     * as it is a backdoor for adding invalid objects.
     *
     * @param <E> the element type
     * @param set  the set to predicate, must not be null
     * @param predicate  the predicate for the set, must not be null
     * @return a predicated set backed by the given set
     * @throws NullPointerException if the set or predicate is null
     */
    public static <E> Set<E> predicatedSet(final Set<E> set, final Predicate<? super E> predicate) {
        return PredicatedSet.predicatedSet(set, predicate);
    }

    /**
     * Returns a predicated (validating) sorted set backed by the given sorted set.
     * <p>
     * Only objects that pass the test in the given predicate can be added to the set.
     * Trying to add an invalid object results in an IllegalArgumentException.
     * It is important not to use the original set after invoking this method,
     * as it is a backdoor for adding invalid objects.
     *
     * @param <E> the element type
     * @param set  the sorted set to predicate, must not be null
     * @param predicate  the predicate for the sorted set, must not be null
     * @return a predicated sorted set backed by the given sorted set
     * @throws NullPointerException if the set or predicate is null
     */
    public static <E> SortedSet<E> predicatedSortedSet(final SortedSet<E> set,
                                                       final Predicate<? super E> predicate) {
        return PredicatedSortedSet.predicatedSortedSet(set, predicate);
    }

    // Set
    //-----------------------------------------------------------------------
    /**
     * Returns a synchronized set backed by the given set.
     * <p>
     * You must manually synchronize on the returned set's iterator to
     * avoid non-deterministic behavior:
     *
     * <pre>
     * Set s = SetUtils.synchronizedSet(mySet);
     * synchronized (s) {
     *     Iterator i = s.iterator();
     *     while (i.hasNext()) {
     *         process (i.next());
     *     }
     * }
     * </pre>
     *
     * This method is just a wrapper for {@link Collections#synchronizedSet(Set)}.
     *
     * @param <E> the element type
     * @param set  the set to synchronize, must not be null
     * @return a synchronized set backed by the given set
     * @throws NullPointerException if the set is null
     */
    public static <E> Set<E> synchronizedSet(final Set<E> set) {
        return Collections.synchronizedSet(set);
    }

    // SortedSet
    //-----------------------------------------------------------------------
    /**
     * Returns a synchronized sorted set backed by the given sorted set.
     * <p>
     * You must manually synchronize on the returned set's iterator to
     * avoid non-deterministic behavior:
     *
     * <pre>
     * Set s = SetUtils.synchronizedSortedSet(mySet);
     * synchronized (s) {
     *     Iterator i = s.iterator();
     *     while (i.hasNext()) {
     *         process (i.next());
     *     }
     * }
     * </pre>
     *
     * This method is just a wrapper for {@link Collections#synchronizedSortedSet(SortedSet)}.
     *
     * @param <E> the element type
     * @param set  the sorted set to synchronize, must not be null
     * @return a synchronized set backed by the given set
     * @throws NullPointerException if the set is null
     */
    public static <E> SortedSet<E> synchronizedSortedSet(final SortedSet<E> set) {
        return Collections.synchronizedSortedSet(set);
    }

    /**
     * Returns a transformed navigable set backed by the given navigable set.
     * <p>
     * Each object is passed through the transformer as it is added to the
     * Set. It is important not to use the original set after invoking this
     * method, as it is a backdoor for adding untransformed objects.
     * <p>
     * Existing entries in the specified set will not be transformed.
     * If you want that behaviour, see {@link TransformedNavigableSet#transformedNavigableSet}.
     *
     * @param <E> the element type
     * @param set  the navigable set to transform, must not be null
     * @param transformer  the transformer for the set, must not be null
     * @return a transformed set backed by the given set
     * @throws NullPointerException if the set or transformer is null
     * @since 4.1
     */
    public static <E> SortedSet<E> transformedNavigableSet(final NavigableSet<E> set,
                                                           final Transformer<? super E, ? extends E> transformer) {
        return TransformedNavigableSet.transformingNavigableSet(set, transformer);
    }

    /**
     * Returns a transformed set backed by the given set.
     * <p>
     * Each object is passed through the transformer as it is added to the
     * Set. It is important not to use the original set after invoking this
     * method, as it is a backdoor for adding untransformed objects.
     * <p>
     * Existing entries in the specified set will not be transformed.
     * If you want that behaviour, see {@link TransformedSet#transformedSet}.
     *
     * @param <E> the element type
     * @param set  the set to transform, must not be null
     * @param transformer  the transformer for the set, must not be null
     * @return a transformed set backed by the given set
     * @throws NullPointerException if the set or transformer is null
     */
    public static <E> Set<E> transformedSet(final Set<E> set,
                                            final Transformer<? super E, ? extends E> transformer) {
        return TransformedSet.transformingSet(set, transformer);
    }

    /**
     * Returns a transformed sorted set backed by the given set.
     * <p>
     * Each object is passed through the transformer as it is added to the
     * Set. It is important not to use the original set after invoking this
     * method, as it is a backdoor for adding untransformed objects.
     * <p>
     * Existing entries in the specified set will not be transformed.
     * If you want that behaviour, see {@link TransformedSortedSet#transformedSortedSet}.
     *
     * @param <E> the element type
     * @param set  the set to transform, must not be null
     * @param transformer  the transformer for the set, must not be null
     * @return a transformed set backed by the given set
     * @throws NullPointerException if the set or transformer is null
     */
    public static <E> SortedSet<E> transformedSortedSet(final SortedSet<E> set,
                                                        final Transformer<? super E, ? extends E> transformer) {
        return TransformedSortedSet.transformingSortedSet(set, transformer);
    }

    // Set operations
    //-----------------------------------------------------------------------

    /**
     * Returns a unmodifiable <b>view</b> of the union of the given {@link Set}s.
     * <p>
     * The returned view contains all elements of {@code a} and {@code b}.
     *
     * @param <E> the generic type that is able to represent the types contained
     *   in both input sets.
     * @param a  the first set, must not be null
     * @param b  the second set, must not be null
     * @return a view of the union of the two set
     * @throws NullPointerException if either input set is null
     * @since 4.1
     */
    public static <E> SetView<E> union(final Set<? extends E> a, final Set<? extends E> b) {
        if (a == null || b == null) {
            throw new NullPointerException("Sets must not be null.");
        }

        final SetView<E> bMinusA = difference(b, a);

        return new SetView<E>() {
            @Override
            public boolean contains(final Object o) {
                return a.contains(o) || b.contains(o);
            }

            @Override
            public Iterator<E> createIterator() {
                return IteratorUtils.chainedIterator(a.iterator(), bMinusA.iterator());
            }

            @Override
            public boolean isEmpty() {
                return a.isEmpty() && b.isEmpty();
            }

            @Override
            public int size() {
                return a.size() + bMinusA.size();
            }
        };
    }

    // NavigableSet
    //-----------------------------------------------------------------------
    /**
     * Returns an unmodifiable navigable set backed by the given navigable set.
     * <p>
     * This method uses the implementation in the decorators subpackage.
     *
     * @param <E> the element type
     * @param set  the navigable set to make unmodifiable, must not be null
     * @return an unmodifiable set backed by the given set
     * @throws NullPointerException if the set is null
     * @since 4.1
     */
    public static <E> SortedSet<E> unmodifiableNavigableSet(final NavigableSet<E> set) {
        return UnmodifiableNavigableSet.unmodifiableNavigableSet(set);
    }

    /**
     * Create an unmodifiable set from the given items. If the passed var-args argument is {@code
     * null}, then the method returns {@code null}.
     * @param <E> the element type
     * @param items the elements that make up the new set
     * @return a set
     * @since 4.3
     */
    public static <E> Set<E> unmodifiableSet(final E... items) {
        if (items == null) {
            return null;
        }
        return UnmodifiableSet.unmodifiableSet(hashSet(items));
    }

    /**
     * Returns an unmodifiable set backed by the given set.
     * <p>
     * This method uses the implementation in the decorators subpackage.
     *
     * @param <E> the element type
     * @param set  the set to make unmodifiable, must not be null
     * @return an unmodifiable set backed by the given set
     * @throws NullPointerException if the set is null
     */
    public static <E> Set<E> unmodifiableSet(final Set<? extends E> set) {
        return UnmodifiableSet.unmodifiableSet(set);
    }

    /**
     * Returns an unmodifiable sorted set backed by the given sorted set.
     * <p>
     * This method uses the implementation in the decorators subpackage.
     *
     * @param <E> the element type
     * @param set  the sorted set to make unmodifiable, must not be null
     * @return an unmodifiable set backed by the given set
     * @throws NullPointerException if the set is null
     */
    public static <E> SortedSet<E> unmodifiableSortedSet(final SortedSet<E> set) {
        return UnmodifiableSortedSet.unmodifiableSortedSet(set);
    }

    /**
     * <code>SetUtils</code> should not normally be instantiated.
     */
    private SetUtils() {}
}
