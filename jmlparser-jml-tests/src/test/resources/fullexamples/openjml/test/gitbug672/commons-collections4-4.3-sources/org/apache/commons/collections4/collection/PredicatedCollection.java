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
package org.apache.commons.collections4.collection;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import org.apache.commons.collections4.Bag;
import org.apache.commons.collections4.MultiSet;
import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.bag.HashBag;
import org.apache.commons.collections4.bag.PredicatedBag;
import org.apache.commons.collections4.functors.NotNullPredicate;
import org.apache.commons.collections4.list.PredicatedList;
import org.apache.commons.collections4.multiset.HashMultiSet;
import org.apache.commons.collections4.multiset.PredicatedMultiSet;
import org.apache.commons.collections4.queue.PredicatedQueue;
import org.apache.commons.collections4.set.PredicatedSet;

/**
 * Decorates another {@link Collection} to validate that additions
 * match a specified predicate.
 * <p>
 * This collection exists to provide validation for the decorated collection.
 * It is normally created to decorate an empty collection.
 * If an object cannot be added to the collection, an IllegalArgumentException is thrown.
 * <p>
 * One usage would be to ensure that no null entries are added to the collection:
 * <pre>
 * Collection coll = PredicatedCollection.predicatedCollection(new ArrayList(), NotNullPredicate.INSTANCE);
 * </pre>
 * <p>
 * This class is Serializable from Commons Collections 3.1.
 *
 * @param <E> the type of the elements in the collection
 * @since 3.0
 */
public class PredicatedCollection<E> extends AbstractCollectionDecorator<E> {

    /** Serialization version */
    private static final long serialVersionUID = -5259182142076705162L;

    /** The predicate to use */
    protected final Predicate<? super E> predicate;

    /**
     * Returns a Builder with the given predicate.
     *
     * @param <E>  the element type
     * @param predicate  the predicate to use
     * @return a new Builder for predicated collections
     * @since 4.1
     */
    public static <E> Builder<E> builder(final Predicate<? super E> predicate) {
        return new Builder<>(predicate);
    }

    /**
     * Returns a Builder with a NotNullPredicate.
     *
     * @param <E>  the element type
     * @return a new Builder for predicated collections that ignores null values.
     * @since 4.1
     */
    public static <E> Builder<E> notNullBuilder() {
        return new Builder<>(NotNullPredicate.<E>notNullPredicate());
    }

    /**
     * Factory method to create a predicated (validating) collection.
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are validated.
     *
     * @param <T> the type of the elements in the collection
     * @param coll  the collection to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @return a new predicated collection
     * @throws NullPointerException if collection or predicate is null
     * @throws IllegalArgumentException if the collection contains invalid elements
     * @since 4.0
     */
    public static <T> PredicatedCollection<T> predicatedCollection(final Collection<T> coll,
                                                                   final Predicate<? super T> predicate) {
        return new PredicatedCollection<>(coll, predicate);
    }

    //-----------------------------------------------------------------------
    /**
     * Constructor that wraps (not copies).
     * <p>
     * If there are any elements already in the collection being decorated, they
     * are validated.
     *
     * @param coll  the collection to decorate, must not be null
     * @param predicate  the predicate to use for validation, must not be null
     * @throws NullPointerException if collection or predicate is null
     * @throws IllegalArgumentException if the collection contains invalid elements
     */
    protected PredicatedCollection(final Collection<E> coll, final Predicate<? super E> predicate) {
        super(coll);
        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null.");
        }
        this.predicate = predicate;
        for (final E item : coll) {
            validate(item);
        }
    }

    /**
     * Validates the object being added to ensure it matches the predicate.
     * <p>
     * The predicate itself should not throw an exception, but return false to
     * indicate that the object cannot be added.
     *
     * @param object  the object being added
     * @throws IllegalArgumentException if the add is invalid
     */
    protected void validate(final E object) {
        if (predicate.evaluate(object) == false) {
            throw new IllegalArgumentException("Cannot add Object '" + object + "' - Predicate '" +
                                               predicate + "' rejected it");
        }
    }

    //-----------------------------------------------------------------------
    /**
     * Override to validate the object being added to ensure it matches
     * the predicate.
     *
     * @param object  the object being added
     * @return the result of adding to the underlying collection
     * @throws IllegalArgumentException if the add is invalid
     */
    @Override
    public boolean add(final E object) {
        validate(object);
        return decorated().add(object);
    }

    /**
     * Override to validate the objects being added to ensure they match
     * the predicate. If any one fails, no update is made to the underlying
     * collection.
     *
     * @param coll  the collection being added
     * @return the result of adding to the underlying collection
     * @throws IllegalArgumentException if the add is invalid
     */
    @Override
    public boolean addAll(final Collection<? extends E> coll) {
        for (final E item : coll) {
            validate(item);
        }
        return decorated().addAll(coll);
    }

    /**
     * Builder for creating predicated collections.
     * <p>
     * Create a Builder with a predicate to validate elements against, then add any elements
     * to the builder. Elements that fail the predicate will be added to a rejected list.
     * Finally create or decorate a collection using the createPredicated[List,Set,Bag,Queue] methods.
     * <p>
     * An example:
     * <pre>
     *   Predicate&lt;String&gt; predicate = NotNullPredicate.notNullPredicate();
     *   PredicatedCollectionBuilder&lt;String&gt; builder = PredicatedCollection.builder(predicate);
     *   builder.add("item1");
     *   builder.add(null);
     *   builder.add("item2");
     *   List&lt;String&gt; predicatedList = builder.createPredicatedList();
     * </pre>
     * <p>
     * At the end of the code fragment above predicatedList is protected by the predicate supplied
     * to the builder and it contains item1 and item2.
     * <p>
     * More elements can be added to the builder once a predicated collection has been created,
     * but these elements will not be reflected in already created collections.
     *
     * @param <E>  the element type
     * @since 4.1
     */
    public static class Builder<E> {

        /** The predicate to use. */
        private final Predicate<? super E> predicate;

        /** The buffer containing valid elements. */
        private final List<E> accepted = new ArrayList<>();

        /** The buffer containing rejected elements. */
        private final List<E> rejected = new ArrayList<>();

        // -----------------------------------------------------------------------
        /**
         * Constructs a PredicatedCollectionBuilder with the specified Predicate.
         *
         * @param predicate  the predicate to use
         * @throws NullPointerException if predicate is null
         */
        public Builder(final Predicate<? super E> predicate) {
            if (predicate == null) {
                throw new NullPointerException("Predicate must not be null");
            }
            this.predicate = predicate;
        }

        /**
         * Adds the item to the builder.
         * <p>
         * If the predicate is true, it is added to the list of accepted elements,
         * otherwise it is added to the rejected list.
         *
         * @param item  the element to add
         * @return the PredicatedCollectionBuilder.
         */
        public Builder<E> add(final E item) {
            if (predicate.evaluate(item)) {
                accepted.add(item);
            } else {
                rejected.add(item);
            }
            return this;
        }

        /**
         * Adds all elements from the given collection to the builder.
         * <p>
         * All elements for which the predicate evaluates to true will be added to the
         * list of accepted elements, otherwise they are added to the rejected list.
         *
         * @param items  the elements to add to the builder
         * @return the PredicatedCollectionBuilder.
         */
        public Builder<E> addAll(final Collection<? extends E> items) {
            if (items != null) {
                for (final E item : items) {
                    add(item);
                }
            }
            return this;
        }

        /**
         * Create a new predicated list filled with the accepted elements.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned list.
         *
         * @return a new predicated list.
         */
        public List<E> createPredicatedList() {
            return createPredicatedList(new ArrayList<E>());
        }

        /**
         * Decorates the given list with validating behavior using the predicate. All accepted elements
         * are appended to the list. If the list already contains elements, they are validated.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned list.
         *
         * @param list  the List to decorate, must not be null
         * @return the decorated list.
         * @throws NullPointerException if list is null
         * @throws IllegalArgumentException if list contains invalid elements
         */
        public List<E> createPredicatedList(final List<E> list) {
            if (list == null) {
                throw new NullPointerException("List must not be null.");
            }
            final List<E> predicatedList = PredicatedList.predicatedList(list, predicate);
            predicatedList.addAll(accepted);
            return predicatedList;
        }

        /**
         * Create a new predicated set filled with the accepted elements.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned set.
         *
         * @return a new predicated set.
         */
        public Set<E> createPredicatedSet() {
            return createPredicatedSet(new HashSet<E>());
        }

        /**
         * Decorates the given list with validating behavior using the predicate. All accepted elements
         * are appended to the set. If the set already contains elements, they are validated.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned set.
         *
         * @param set  the set to decorate, must not be null
         * @return the decorated set.
         * @throws NullPointerException if set is null
         * @throws IllegalArgumentException if set contains invalid elements
         */
        public Set<E> createPredicatedSet(final Set<E> set) {
            if (set == null) {
                throw new NullPointerException("Set must not be null.");
            }
            final PredicatedSet<E> predicatedSet = PredicatedSet.predicatedSet(set, predicate);
            predicatedSet.addAll(accepted);
            return predicatedSet;
        }

        /**
         * Create a new predicated multiset filled with the accepted elements.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned multiset.
         *
         * @return a new predicated multiset.
         */
        public MultiSet<E> createPredicatedMultiSet() {
            return createPredicatedMultiSet(new HashMultiSet<E>());
        }

        /**
         * Decorates the given multiset with validating behavior using the predicate. All accepted elements
         * are appended to the multiset. If the multiset already contains elements, they are validated.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned multiset.
         *
         * @param multiset  the multiset to decorate, must not be null
         * @return the decorated multiset.
         * @throws NullPointerException if multiset is null
         * @throws IllegalArgumentException if multiset contains invalid elements
         */
        public MultiSet<E> createPredicatedMultiSet(final MultiSet<E> multiset) {
            if (multiset == null) {
                throw new NullPointerException("MultiSet must not be null.");
            }
            final PredicatedMultiSet<E> predicatedMultiSet =
                    PredicatedMultiSet.predicatedMultiSet(multiset, predicate);
            predicatedMultiSet.addAll(accepted);
            return predicatedMultiSet;
        }

        /**
         * Create a new predicated bag filled with the accepted elements.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned bag.
         *
         * @return a new predicated bag.
         */
        public Bag<E> createPredicatedBag() {
            return createPredicatedBag(new HashBag<E>());
        }

        /**
         * Decorates the given bag with validating behavior using the predicate. All accepted elements
         * are appended to the bag. If the bag already contains elements, they are validated.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned bag.
         *
         * @param bag  the bag to decorate, must not be null
         * @return the decorated bag.
         * @throws NullPointerException if bag is null
         * @throws IllegalArgumentException if bag contains invalid elements
         */
        public Bag<E> createPredicatedBag(final Bag<E> bag) {
            if (bag == null) {
                throw new NullPointerException("Bag must not be null.");
            }
            final PredicatedBag<E> predicatedBag = PredicatedBag.predicatedBag(bag, predicate);
            predicatedBag.addAll(accepted);
            return predicatedBag;
        }

        /**
         * Create a new predicated queue filled with the accepted elements.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned queue.
         *
         * @return a new predicated queue.
         */
        public Queue<E> createPredicatedQueue() {
            return createPredicatedQueue(new LinkedList<E>());
        }

        /**
         * Decorates the given queue with validating behavior using the predicate. All accepted elements
         * are appended to the queue. If the queue already contains elements, they are validated.
         * <p>
         * The builder is not modified by this method, so it is possible to create more collections
         * or add more elements afterwards. Further changes will not propagate to the returned queue.
         *
         * @param queue  the queue to decorate, must not be null
         * @return the decorated queue.
         * @throws NullPointerException if queue is null
         * @throws IllegalArgumentException if queue contains invalid elements
         */
        public Queue<E> createPredicatedQueue(final Queue<E> queue) {
            if (queue == null) {
                throw new NullPointerException("queue must not be null");
            }
            final PredicatedQueue<E> predicatedQueue = PredicatedQueue.predicatedQueue(queue, predicate);
            predicatedQueue.addAll(accepted);
            return predicatedQueue;
        }

        /**
         * Returns an unmodifiable collection containing all rejected elements.
         *
         * @return an unmodifiable collection
         */
        public Collection<E> rejectedElements() {
            return Collections.unmodifiableCollection(rejected);
        }

    }

}
