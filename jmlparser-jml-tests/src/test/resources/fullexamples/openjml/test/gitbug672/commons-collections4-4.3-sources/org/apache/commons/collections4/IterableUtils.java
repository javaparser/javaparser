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

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import org.apache.commons.collections4.functors.EqualPredicate;
import org.apache.commons.collections4.iterators.LazyIteratorChain;
import org.apache.commons.collections4.iterators.ReverseListIterator;
import org.apache.commons.collections4.iterators.UniqueFilterIterator;

/**
 * Provides utility methods and decorators for {@link Iterable} instances.
 * <p>
 * <b>Note</b>: this util class has been designed for fail-fast argument checking.
 * <ul>
 * <li>
 * all decorator methods are <b>NOT</b> null-safe wrt the provided Iterable argument, i.e.
 * they will throw a {@link NullPointerException} if a null Iterable is passed as argument.
 * <li>
 * all other utility methods are null-safe wrt the provided Iterable argument, i.e. they will
 * treat a null Iterable the same way as an empty one. Other arguments which are null,
 * e.g. a {@link Predicate}, will result in a {@link NullPointerException}. Exception: passing
 * a null {@link Comparator} is equivalent to a Comparator with natural ordering.
 * </ul>
 *
 * @since 4.1
 */
public class IterableUtils {

    /**
     * An empty iterable.
     */
    @SuppressWarnings("rawtypes")
    static final FluentIterable EMPTY_ITERABLE = new FluentIterable<Object>() {
        @Override
        public Iterator<Object> iterator() {
            return IteratorUtils.emptyIterator();
        }
    };

    // Empty
    // ----------------------------------------------------------------------

    /**
     * Gets an empty iterable.
     * <p>
     * This iterable does not contain any elements.
     *
     * @param <E> the element type
     * @return an empty iterable
     */
    @SuppressWarnings("unchecked") // OK, empty collection is compatible with any type
    public static <E> Iterable<E> emptyIterable() {
        return EMPTY_ITERABLE;
    }

    // Chained
    // ----------------------------------------------------------------------

    /**
     * Combines two iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in {@code a},
     * followed by the elements in {@code b}. The source iterators are not polled until
     * necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @return a new iterable, combining the provided iterables
     * @throws NullPointerException if either a or b is null
     */
    @SuppressWarnings("unchecked")
    public static <E> Iterable<E> chainedIterable(final Iterable<? extends E> a,
                                                  final Iterable<? extends E> b) {
        return chainedIterable(new Iterable[] {a, b});
    }

    /**
     * Combines three iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in {@code a},
     * followed by the elements in {@code b} and {@code c}. The source iterators are
     * not polled until necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @param c  the third iterable, may not be null
     * @return a new iterable, combining the provided iterables
     * @throws NullPointerException if either of the provided iterables is null
     */
    @SuppressWarnings("unchecked")
    public static <E> Iterable<E> chainedIterable(final Iterable<? extends E> a,
                                                  final Iterable<? extends E> b,
                                                  final Iterable<? extends E> c) {
        return chainedIterable(new Iterable[] {a, b, c});
    }

    /**
     * Combines four iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in {@code a},
     * followed by the elements in {@code b}, {@code c} and {@code d}. The source
     * iterators are not polled until necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @param c  the third iterable, may not be null
     * @param d  the fourth iterable, may not be null
     * @return a new iterable, combining the provided iterables
     * @throws NullPointerException if either of the provided iterables is null
     */
    @SuppressWarnings("unchecked")
    public static <E> Iterable<E> chainedIterable(final Iterable<? extends E> a,
                                                  final Iterable<? extends E> b,
                                                  final Iterable<? extends E> c,
                                                  final Iterable<? extends E> d) {
        return chainedIterable(new Iterable[] {a, b, c, d});
    }

    /**
     * Combines the provided iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in the order
     * of the arguments, i.e. iterables[0], iterables[1], .... The source iterators
     * are not polled until necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param iterables  the iterables to combine, may not be null
     * @return a new iterable, combining the provided iterables
     * @throws NullPointerException if either of the provided iterables is null
     */
    public static <E> Iterable<E> chainedIterable(final Iterable<? extends E>... iterables) {
        checkNotNull(iterables);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return new LazyIteratorChain<E>() {
                    @Override
                    protected Iterator<? extends E> nextIterator(final int count) {
                        if (count > iterables.length) {
                            return null;
                        }
                        return iterables[count - 1].iterator();
                    }
                };
            }
        };
    }

    // Collated
    // ----------------------------------------------------------------------

    /**
     * Combines the two provided iterables into an ordered iterable using
     * natural ordering.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the
     * corresponding input iterator supports it.
     *
     * @param <E> the element type
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @return a filtered view on the specified iterable
     * @throws NullPointerException if either of the provided iterables is null
     */
    public static <E> Iterable<E> collatedIterable(final Iterable<? extends E> a,
                                                   final Iterable<? extends E> b) {
        checkNotNull(a, b);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.collatedIterator(null, a.iterator(), b.iterator());
            }
        };
    }

    /**
     * Combines the two provided iterables into an ordered iterable using the
     * provided comparator. If the comparator is null, natural ordering will be
     * used.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the
     * corresponding input iterator supports it.
     *
     * @param <E> the element type
     * @param comparator  the comparator defining an ordering over the elements,
     *   may be null, in which case natural ordering will be used
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @return a filtered view on the specified iterable
     * @throws NullPointerException if either of the provided iterables is null
     */
    public static <E> Iterable<E> collatedIterable(final Comparator<? super E> comparator,
                                                   final Iterable<? extends E> a,
                                                   final Iterable<? extends E> b) {
        checkNotNull(a, b);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.collatedIterator(comparator, a.iterator(), b.iterator());
            }
        };
    }

    // Filtered
    // ----------------------------------------------------------------------

    /**
     * Returns a view of the given iterable that only contains elements matching
     * the provided predicate.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the
     * corresponding input iterator supports it.
     *
     * @param <E> the element type
     * @param iterable  the iterable to filter, may not be null
     * @param predicate  the predicate used to filter elements, may not be null
     * @return a filtered view on the specified iterable
     * @throws NullPointerException if either iterable or predicate is null
     */
    public static <E> Iterable<E> filteredIterable(final Iterable<E> iterable,
                                                   final Predicate<? super E> predicate) {
        checkNotNull(iterable);
        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null.");
        }
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.filteredIterator(emptyIteratorIfNull(iterable), predicate);
            }
        };
    }

    // Bounded
    // ----------------------------------------------------------------------

    /**
     * Returns a view of the given iterable that contains at most the given number
     * of elements.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param iterable  the iterable to limit, may not be null
     * @param maxSize  the maximum number of elements, must not be negative
     * @return a bounded view on the specified iterable
     * @throws IllegalArgumentException if maxSize is negative
     * @throws NullPointerException if iterable is null
     */
    public static <E> Iterable<E> boundedIterable(final Iterable<E> iterable, final long maxSize) {
        checkNotNull(iterable);
        if (maxSize < 0) {
            throw new IllegalArgumentException("MaxSize parameter must not be negative.");
        }

        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.boundedIterator(iterable.iterator(), maxSize);
            }
        };
    }

    // Looping
    // ----------------------------------------------------------------------

    /**
     * Returns a view of the given iterable which will cycle infinitely over
     * its elements.
     * <p>
     * The returned iterable's iterator supports {@code remove()} if
     * {@code iterable.iterator()} does. After {@code remove()} is called, subsequent
     * cycles omit the removed element, which is no longer in {@code iterable}. The
     * iterator's {@code hasNext()} method returns {@code true} until {@code iterable}
     * is empty.
     *
     * @param <E> the element type
     * @param iterable  the iterable to loop, may not be null
     * @return a view of the iterable, providing an infinite loop over its elements
     * @throws NullPointerException if iterable is null
     */
    public static <E> Iterable<E> loopingIterable(final Iterable<E> iterable) {
        checkNotNull(iterable);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return new LazyIteratorChain<E>() {
                    @Override
                    protected Iterator<? extends E> nextIterator(final int count) {
                        if (IterableUtils.isEmpty(iterable)) {
                            return null;
                        }
                        return iterable.iterator();
                    }
                };
            }
        };
    }

    // Reversed
    // ----------------------------------------------------------------------

    /**
     * Returns a reversed view of the given iterable.
     * <p>
     * In case the provided iterable is a {@link List} instance, a
     * {@link ReverseListIterator} will be used to reverse the traversal
     * order, otherwise an intermediate {@link List} needs to be created.
     * <p>
     * The returned iterable's iterator supports {@code remove()} if the
     * provided iterable is a {@link List} instance.
     *
     * @param <E> the element type
     * @param iterable  the iterable to use, may not be null
     * @return a reversed view of the specified iterable
     * @throws NullPointerException if iterable is null
     * @see ReverseListIterator
     */
    public static <E> Iterable<E> reversedIterable(final Iterable<E> iterable) {
        checkNotNull(iterable);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                final List<E> list = (iterable instanceof List<?>) ?
                        (List<E>) iterable :
                        IteratorUtils.toList(iterable.iterator());
                return new ReverseListIterator<>(list);
            }
        };
    }

    // Skipping
    // ----------------------------------------------------------------------

    /**
     * Returns a view of the given iterable that skips the first N elements.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param iterable  the iterable to use, may not be null
     * @param elementsToSkip  the number of elements to skip from the start, must not be negative
     * @return a view of the specified iterable, skipping the first N elements
     * @throws IllegalArgumentException if elementsToSkip is negative
     * @throws NullPointerException if iterable is null
     */
    public static <E> Iterable<E> skippingIterable(final Iterable<E> iterable, final long elementsToSkip) {
        checkNotNull(iterable);
        if (elementsToSkip < 0) {
            throw new IllegalArgumentException("ElementsToSkip parameter must not be negative.");
        }

        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.skippingIterator(iterable.iterator(), elementsToSkip);
            }
        };
    }

    // Transformed
    // ----------------------------------------------------------------------

    /**
     * Returns a transformed view of the given iterable where all of its elements
     * have been transformed by the provided transformer.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <I>  the input element type
     * @param <O>  the output element type
     * @param iterable  the iterable to transform, may not be null
     * @param transformer  the transformer, must not be null
     * @return a transformed view of the specified iterable
     * @throws NullPointerException if either iterable or transformer is null
     */
    public static <I, O> Iterable<O> transformedIterable(final Iterable<I> iterable,
                                                         final Transformer<? super I, ? extends O> transformer) {
        checkNotNull(iterable);
        if (transformer == null) {
            throw new NullPointerException("Transformer must not be null.");
        }
        return new FluentIterable<O>() {
            @Override
            public Iterator<O> iterator() {
                return IteratorUtils.transformedIterator(iterable.iterator(), transformer);
            }
        };
    }

    // Unique
    // ----------------------------------------------------------------------

    /**
     * Returns a unique view of the given iterable.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the
     * corresponding input iterator supports it. Calling {@code remove()}
     * will only remove a single element from the underlying iterator.
     *
     * @param <E> the element type
     * @param iterable  the iterable to use, may not be null
     * @return a unique view of the specified iterable
     * @throws NullPointerException if iterable is null
     */
    public static <E> Iterable<E> uniqueIterable(final Iterable<E> iterable) {
        checkNotNull(iterable);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return new UniqueFilterIterator<>(iterable.iterator());
            }
        };
    }

    // Unmodifiable
    // ----------------------------------------------------------------------

    /**
     * Returns an unmodifiable view of the given iterable.
     * <p>
     * The returned iterable's iterator does not support {@code remove()}.
     *
     * @param <E> the element type
     * @param iterable  the iterable to use, may not be null
     * @return an unmodifiable view of the specified iterable
     * @throws NullPointerException if iterable is null
     */
    public static <E> Iterable<E> unmodifiableIterable(final Iterable<E> iterable) {
        checkNotNull(iterable);
        if (iterable instanceof UnmodifiableIterable<?>) {
            return iterable;
        }
        return new UnmodifiableIterable<>(iterable);
    }

    /**
     * Inner class to distinguish unmodifiable instances.
     */
    private static final class UnmodifiableIterable<E> extends FluentIterable<E> {
        private final Iterable<E> unmodifiable;

        public UnmodifiableIterable(final Iterable<E> iterable) {
            super();
            this.unmodifiable = iterable;
        }

        @Override
        public Iterator<E> iterator() {
            return IteratorUtils.unmodifiableIterator(unmodifiable.iterator());
        }
    }

    // Zipping
    // ----------------------------------------------------------------------

    /**
     * Interleaves two iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in {@code a}
     * and {@code b} in alternating order. The source iterators are not polled until
     * necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param a  the first iterable, may not be null
     * @param b  the second iterable, may not be null
     * @return a new iterable, interleaving the provided iterables
     * @throws NullPointerException if either a or b is null
     */
    public static <E> Iterable<E> zippingIterable(final Iterable<? extends E> a,
                                                  final Iterable<? extends E> b) {
        checkNotNull(a);
        checkNotNull(b);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                return IteratorUtils.zippingIterator(a.iterator(), b.iterator());
            }
        };
    }

    /**
     * Interleaves two iterables into a single iterable.
     * <p>
     * The returned iterable has an iterator that traverses the elements in {@code a}
     * and {@code b} in alternating order. The source iterators are not polled until
     * necessary.
     * <p>
     * The returned iterable's iterator supports {@code remove()} when the corresponding
     * input iterator supports it.
     *
     * @param <E> the element type
     * @param first  the first iterable, may not be null
     * @param others  the array of iterables to interleave, may not be null
     * @return a new iterable, interleaving the provided iterables
     * @throws NullPointerException if either of the provided iterables is null
     */
    public static <E> Iterable<E> zippingIterable(final Iterable<? extends E> first,
                                                  final Iterable<? extends E>... others) {
        checkNotNull(first);
        checkNotNull(others);
        return new FluentIterable<E>() {
            @Override
            public Iterator<E> iterator() {
                @SuppressWarnings("unchecked") // safe
                final
                Iterator<? extends E>[] iterators = new Iterator[others.length + 1];
                iterators[0] = first.iterator();
                for (int i = 0; i < others.length; i++) {
                    iterators[i + 1] = others[i].iterator();
                }
                return IteratorUtils.zippingIterator(iterators);
            }
        };
    }

    // Utility methods
    // ----------------------------------------------------------------------

    /**
     * Returns an immutable empty iterable if the argument is null,
     * or the argument itself otherwise.
     *
     * @param <E> the element type
     * @param iterable  the iterable, may be null
     * @return an empty iterable if the argument is null
     */
    public static <E> Iterable<E> emptyIfNull(final Iterable<E> iterable) {
        return iterable == null ? IterableUtils.<E>emptyIterable() : iterable;
    }

    /**
     * Applies the closure to each element of the provided iterable.
     *
     * @param <E> the element type
     * @param iterable  the iterator to use, may be null
     * @param closure  the closure to apply to each element, may not be null
     * @throws NullPointerException if closure is null
     */
    public static <E> void forEach(final Iterable<E> iterable, final Closure<? super E> closure) {
        IteratorUtils.forEach(emptyIteratorIfNull(iterable), closure);
    }

    /**
     * Executes the given closure on each but the last element in the iterable.
     * <p>
     * If the input iterable is null no change is made.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param iterable  the iterable to get the input from, may be null
     * @param closure  the closure to perform, may not be null
     * @return the last element in the iterable, or null if iterable is null or empty
     */
    public static <E> E forEachButLast(final Iterable<E> iterable, final Closure<? super E> closure) {
        return IteratorUtils.forEachButLast(emptyIteratorIfNull(iterable), closure);
    }

    /**
     * Finds the first element in the given iterable which matches the given predicate.
     * <p>
     * A <code>null</code> or empty iterator returns null.
     *
     * @param <E> the element type
     * @param iterable  the iterable to search, may be null
     * @param predicate  the predicate to use, may not be null
     * @return the first element of the iterable which matches the predicate or null if none could be found
     * @throws NullPointerException if predicate is null
     */
    public static <E> E find(final Iterable<E> iterable, final Predicate<? super E> predicate) {
        return IteratorUtils.find(emptyIteratorIfNull(iterable), predicate);
    }

    /**
     * Returns the index of the first element in the specified iterable that
     * matches the given predicate.
     * <p>
     * A <code>null</code> or empty iterable returns -1.
     *
     * @param <E> the element type
     * @param iterable  the iterable to search, may be null
     * @param predicate  the predicate to use, may not be null
     * @return the index of the first element which matches the predicate or -1 if none matches
     * @throws NullPointerException if predicate is null
     */
    public static <E> int indexOf(final Iterable<E> iterable, final Predicate<? super E> predicate) {
        return IteratorUtils.indexOf(emptyIteratorIfNull(iterable), predicate);
    }

    /**
     * Answers true if a predicate is true for every element of an iterable.
     * <p>
     * A <code>null</code> or empty iterable returns true.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param iterable  the {@link Iterable} to use, may be null
     * @param predicate  the predicate to use, may not be null
     * @return true if every element of the collection matches the predicate or if the
     *   collection is empty, false otherwise
     * @throws NullPointerException if predicate is null
     */
    public static <E> boolean matchesAll(final Iterable<E> iterable, final Predicate<? super E> predicate) {
        return IteratorUtils.matchesAll(emptyIteratorIfNull(iterable), predicate);
    }

    /**
     * Answers true if a predicate is true for any element of the iterable.
     * <p>
     * A <code>null</code> or empty iterable returns false.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param iterable  the {@link Iterable} to use, may be null
     * @param predicate  the predicate to use, may not be null
     * @return true if any element of the collection matches the predicate, false otherwise
     * @throws NullPointerException if predicate is null
     */
    public static <E> boolean matchesAny(final Iterable<E> iterable, final Predicate<? super E> predicate) {
        return IteratorUtils.matchesAny(emptyIteratorIfNull(iterable), predicate);
    }

    /**
     * Counts the number of elements in the input iterable that match the predicate.
     * <p>
     * A <code>null</code> iterable matches no elements.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param input  the {@link Iterable} to get the input from, may be null
     * @param predicate  the predicate to use, may not be null
     * @return the number of matches for the predicate in the collection
     * @throws NullPointerException if predicate is null
     */
    public static <E> long countMatches(final Iterable<E> input, final Predicate<? super E> predicate) {
        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null.");
        }
        return size(filteredIterable(emptyIfNull(input), predicate));
    }

    /**
     * Answers true if the provided iterable is empty.
     * <p>
     * A <code>null</code> iterable returns true.
     *
     * @param iterable  the {@link Iterable to use}, may be null
     * @return true if the iterable is null or empty, false otherwise
     */
    public static boolean isEmpty(final Iterable<?> iterable) {
        if (iterable instanceof Collection<?>) {
            return ((Collection<?>) iterable).isEmpty();
        }
        return IteratorUtils.isEmpty(emptyIteratorIfNull(iterable));
    }

    /**
     * Checks if the object is contained in the given iterable.
     * <p>
     * A <code>null</code> or empty iterable returns false.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param iterable  the iterable to check, may be null
     * @param object  the object to check
     * @return true if the object is contained in the iterable, false otherwise
     */
    public static <E> boolean contains(final Iterable<E> iterable, final Object object) {
        if (iterable instanceof Collection<?>) {
            return ((Collection<E>) iterable).contains(object);
        }
        return IteratorUtils.contains(emptyIteratorIfNull(iterable), object);
    }

    /**
     * Checks if the object is contained in the given iterable. Object equality
     * is tested with an {@code equator} unlike {@link #contains(Iterable, Object)}
     * which uses {@link Object#equals(Object)}.
     * <p>
     * A <code>null</code> or empty iterable returns false.
     * A <code>null</code> object will not be passed to the equator, instead a
     * {@link org.apache.commons.collections4.functors.NullPredicate NullPredicate}
     * will be used.
     *
     * @param <E> the type of object the {@link Iterable} contains
     * @param iterable  the iterable to check, may be null
     * @param object  the object to check
     * @param equator  the equator to use to check, may not be null
     * @return true if the object is contained in the iterable, false otherwise
     * @throws NullPointerException if equator is null
     */
    public static <E> boolean contains(final Iterable<? extends E> iterable, final E object,
                                       final Equator<? super E> equator) {
        if (equator == null) {
            throw new NullPointerException("Equator must not be null.");
        }
        return matchesAny(iterable, EqualPredicate.equalPredicate(object, equator));
    }

    /**
     * Returns the number of occurrences of the provided object in the iterable.
     *
     * @param <E> the element type that the {@link Iterable} may contain
     * @param <T> the element type of the object to find
     * @param iterable  the {@link Iterable} to search
     * @param obj  the object to find the cardinality of
     * @return the number of occurrences of obj in iterable
     */
    public static <E, T extends E> int frequency(final Iterable<E> iterable, final T obj) {
        if (iterable instanceof Set<?>) {
            return ((Set<E>) iterable).contains(obj) ? 1 : 0;
        }
        if (iterable instanceof Bag<?>) {
            return ((Bag<E>) iterable).getCount(obj);
        }
        return size(filteredIterable(emptyIfNull(iterable), EqualPredicate.<E>equalPredicate(obj)));
    }

    /**
     * Returns the <code>index</code>-th value in the <code>iterable</code>'s {@link Iterator}, throwing
     * <code>IndexOutOfBoundsException</code> if there is no such element.
     * <p>
     * If the {@link Iterable} is a {@link List}, then it will use {@link List#get(int)}.
     *
     * @param <T> the type of object in the {@link Iterable}.
     * @param iterable  the {@link Iterable} to get a value from, may be null
     * @param index  the index to get
     * @return the object at the specified index
     * @throws IndexOutOfBoundsException if the index is invalid
     */
    public static <T> T get(final Iterable<T> iterable, final int index) {
        CollectionUtils.checkIndexBounds(index);
        if (iterable instanceof List<?>) {
            return ((List<T>) iterable).get(index);
        }
        return IteratorUtils.get(emptyIteratorIfNull(iterable), index);
    }

    /**
     * Shortcut for {@code get(iterator, 0)}.
     * <p>
     * Returns the <code>first</code> value in the <code>iterable</code>'s {@link Iterator}, throwing
     * <code>IndexOutOfBoundsException</code> if there is no such element.
     * </p>
     * <p>
     * If the {@link Iterable} is a {@link List}, then it will use {@link List#get(int)}.
     * </p>
     *
     * @param <T> the type of object in the {@link Iterable}.
     * @param iterable  the {@link Iterable} to get a value from, may be null
     * @return the first object
     * @throws IndexOutOfBoundsException if the request  is invalid
     * @since 4.2
     */
    public static <T> T first(final Iterable<T> iterable) {
        return get(iterable, 0);
    }

    /**
     * Returns the number of elements contained in the given iterator.
     * <p>
     * A <code>null</code> or empty iterator returns {@code 0}.
     *
     * @param iterable  the iterable to check, may be null
     * @return the number of elements contained in the iterable
     */
    public static int size(final Iterable<?> iterable) {
        if (iterable instanceof Collection<?>) {
            return ((Collection<?>) iterable).size();
        }
        return IteratorUtils.size(emptyIteratorIfNull(iterable));
    }

    /**
     * Partitions all elements from iterable into separate output collections,
     * based on the evaluation of the given predicate.
     * <p>
     * For each predicate, the result will contain a list holding all elements of the
     * input iterable matching the predicate. The last list will hold all elements
     * which didn't match any predicate:
     * <pre>
     *  [C1, R] = partition(I, P1) with
     *  I = input
     *  P1 = first predicate
     *  C1 = collection of elements matching P1
     *  R = collection of elements rejected by all predicates
     * </pre>
     * <p>
     * If the input iterable is <code>null</code>, the same is returned as for an
     * empty iterable.
     * <p>
     * Example: for an input list [1, 2, 3, 4, 5] calling partition with a predicate [x &lt; 3]
     * will result in the following output: [[1, 2], [3, 4, 5]].
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param iterable  the iterable to partition, may be null
     * @param predicate  the predicate to use, may not be null
     * @return a list containing the output collections
     * @throws NullPointerException if predicate is null
     */
    public static <O> List<List<O>> partition(final Iterable<? extends O> iterable,
                                              final Predicate<? super O> predicate) {
        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null.");
        }
        @SuppressWarnings({ "unchecked", "rawtypes" }) // safe
        final Factory<List<O>> factory = FactoryUtils.instantiateFactory((Class) ArrayList.class);
        @SuppressWarnings("unchecked") // safe
        final Predicate<? super O>[] predicates = new Predicate[] { predicate };
        return partition(iterable, factory, predicates);
    }

    /**
     * Partitions all elements from iterable into separate output collections,
     * based on the evaluation of the given predicates.
     * <p>
     * For each predicate, the result will contain a list holding all elements of the
     * input iterable matching the predicate. The last list will hold all elements
     * which didn't match any predicate:
     * <pre>
     *  [C1, C2, R] = partition(I, P1, P2) with
     *  I = input
     *  P1 = first predicate
     *  P2 = second predicate
     *  C1 = collection of elements matching P1
     *  C2 = collection of elements matching P2
     *  R = collection of elements rejected by all predicates
     * </pre>
     * <p>
     * <b>Note</b>: elements are only added to the output collection of the first matching
     * predicate, determined by the order of arguments.
     * <p>
     * If the input iterable is <code>null</code>, the same is returned as for an
     * empty iterable.
     * <p>
     * Example: for an input list [1, 2, 3, 4, 5] calling partition with predicates [x &lt; 3]
     * and [x &lt; 5] will result in the following output: [[1, 2], [3, 4], [5]].
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param iterable  the collection to get the input from, may be null
     * @param predicates  the predicates to use, may not be null
     * @return a list containing the output collections
     * @throws NullPointerException if any predicate is null
     */
    public static <O> List<List<O>> partition(final Iterable<? extends O> iterable,
                                              final Predicate<? super O>... predicates) {

        @SuppressWarnings({ "unchecked", "rawtypes" }) // safe
        final Factory<List<O>> factory = FactoryUtils.instantiateFactory((Class) ArrayList.class);
        return partition(iterable, factory, predicates);
    }

    /**
     * Partitions all elements from iterable into separate output collections,
     * based on the evaluation of the given predicates.
     * <p>
     * For each predicate, the returned list will contain a collection holding
     * all elements of the input iterable matching the predicate. The last collection
     * contained in the list will hold all elements which didn't match any predicate:
     * <pre>
     *  [C1, C2, R] = partition(I, P1, P2) with
     *  I = input
     *  P1 = first predicate
     *  P2 = second predicate
     *  C1 = collection of elements matching P1
     *  C2 = collection of elements matching P2
     *  R = collection of elements rejected by all predicates
     * </pre>
     * <p>
     * <b>Note</b>: elements are only added to the output collection of the first matching
     * predicate, determined by the order of arguments.
     * <p>
     * If the input iterable is <code>null</code>, the same is returned as for an
     * empty iterable.
     * If no predicates have been provided, all elements of the input collection
     * will be added to the rejected collection.
     * <p>
     * Example: for an input list [1, 2, 3, 4, 5] calling partition with predicates [x &lt; 3]
     * and [x &lt; 5] will result in the following output: [[1, 2], [3, 4], [5]].
     *
     * @param <O>  the type of object the {@link Iterable} contains
     * @param <R>  the type of the output {@link Collection}
     * @param iterable  the collection to get the input from, may be null
     * @param partitionFactory  the factory used to create the output collections
     * @param predicates  the predicates to use, may not be null
     * @return a list containing the output collections
     * @throws NullPointerException if any predicate is null
     */
    public static <O, R extends Collection<O>> List<R> partition(final Iterable<? extends O> iterable,
            final Factory<R> partitionFactory, final Predicate<? super O>... predicates) {

        if (iterable == null) {
            final Iterable<O> empty = emptyIterable();
            return partition(empty, partitionFactory, predicates);
        }

        if (predicates == null) {
            throw new NullPointerException("Predicates must not be null.");
        }

        for (final Predicate<?> p : predicates) {
            if (p == null) {
                throw new NullPointerException("Predicate must not be null.");
            }
        }

        if (predicates.length < 1) {
            // return the entire input collection as a single partition
            final R singlePartition = partitionFactory.create();
            CollectionUtils.addAll(singlePartition, iterable);
            return Collections.singletonList(singlePartition);
        }

        // create the empty partitions
        final int numberOfPredicates = predicates.length;
        final int numberOfPartitions = numberOfPredicates + 1;
        final List<R> partitions = new ArrayList<>(numberOfPartitions);
        for (int i = 0; i < numberOfPartitions; ++i) {
            partitions.add(partitionFactory.create());
        }

        // for each element in inputCollection:
        // find the first predicate that evaluates to true.
        // if there is a predicate, add the element to the corresponding partition.
        // if there is no predicate, add it to the last, catch-all partition.
        for (final O element : iterable) {
            boolean elementAssigned = false;
            for (int i = 0; i < numberOfPredicates; ++i) {
                if (predicates[i].evaluate(element)) {
                    partitions.get(i).add(element);
                    elementAssigned = true;
                    break;
                }
            }

            if (!elementAssigned) {
                // no predicates evaluated to true
                // add element to last partition
                partitions.get(numberOfPredicates).add(element);
            }
        }

        return partitions;
    }

    /**
     * Gets a new list with the contents of the provided iterable.
     *
     * @param <E> the element type
     * @param iterable  the iterable to use, may be null
     * @return a list of the iterator contents
     */
    public static <E> List<E> toList(final Iterable<E> iterable) {
        return IteratorUtils.toList(emptyIteratorIfNull(iterable));
    }

    /**
     * Returns a string representation of the elements of the specified iterable.
     * <p>
     * The string representation consists of a list of the iterable's elements,
     * enclosed in square brackets ({@code "[]"}). Adjacent elements are separated
     * by the characters {@code ", "} (a comma followed by a space). Elements are
     * converted to strings as by {@code String.valueOf(Object)}.
     *
     * @param <E> the element type
     * @param iterable  the iterable to convert to a string, may be null
     * @return a string representation of {@code iterable}
     */
    public static <E> String toString(final Iterable<E> iterable) {
        return IteratorUtils.toString(emptyIteratorIfNull(iterable));
    }

    /**
     * Returns a string representation of the elements of the specified iterable.
     * <p>
     * The string representation consists of a list of the iterable's elements,
     * enclosed in square brackets ({@code "[]"}). Adjacent elements are separated
     * by the characters {@code ", "} (a comma followed by a space). Elements are
     * converted to strings as by using the provided {@code transformer}.
     *
     * @param <E> the element type
     * @param iterable  the iterable to convert to a string, may be null
     * @param transformer  the transformer used to get a string representation of an element
     * @return a string representation of {@code iterable}
     * @throws NullPointerException if {@code transformer} is null
     */
    public static <E> String toString(final Iterable<E> iterable,
                                      final Transformer<? super E, String> transformer) {
        if (transformer == null) {
            throw new NullPointerException("Transformer must not be null.");
        }
        return IteratorUtils.toString(emptyIteratorIfNull(iterable), transformer);
    }

    /**
     * Returns a string representation of the elements of the specified iterable.
     * <p>
     * The string representation consists of a list of the iterable's elements,
     * enclosed by the provided {@code prefix} and {@code suffix}. Adjacent elements
     * are separated by the provided {@code delimiter}. Elements are converted to
     * strings as by using the provided {@code transformer}.
     *
     * @param <E> the element type
     * @param iterable  the iterable to convert to a string, may be null
     * @param transformer  the transformer used to get a string representation of an element
     * @param delimiter  the string to delimit elements
     * @param prefix  the prefix, prepended to the string representation
     * @param suffix  the suffix, appended to the string representation
     * @return a string representation of {@code iterable}
     * @throws NullPointerException if either transformer, delimiter, prefix or suffix is null
     */
    public static <E> String toString(final Iterable<E> iterable,
                                      final Transformer<? super E, String> transformer,
                                      final String delimiter,
                                      final String prefix,
                                      final String suffix) {
        return IteratorUtils.toString(emptyIteratorIfNull(iterable),
                                      transformer, delimiter, prefix, suffix);
    }

    // Helper methods
    // ----------------------------------------------------------------------

    /**
     * Fail-fast check for null arguments.
     *
     * @param iterable  the iterable to check
     * @throws NullPointerException if iterable is null
     */
    static void checkNotNull(final Iterable<?> iterable) {
        if (iterable == null) {
            throw new NullPointerException("Iterable must not be null.");
        }
    }

    /**
     * Fail-fast check for null arguments.
     *
     * @param iterables  the iterables to check
     * @throws NullPointerException if the argument or any of its contents is null
     */
    static void checkNotNull(final Iterable<?>... iterables) {
        if (iterables == null) {
            throw new NullPointerException("Iterables must not be null.");
        }
        for (final Iterable<?> iterable : iterables) {
            checkNotNull(iterable);
        }
    }

    /**
     * Returns an empty iterator if the argument is <code>null</code>,
     * or {@code iterable.iterator()} otherwise.
     *
     * @param <E> the element type
     * @param iterable  the iterable, possibly <code>null</code>
     * @return an empty iterator if the argument is <code>null</code>
     */
    private static <E> Iterator<E> emptyIteratorIfNull(final Iterable<E> iterable) {
        return iterable != null ? iterable.iterator() : IteratorUtils.<E>emptyIterator();
    }

}
