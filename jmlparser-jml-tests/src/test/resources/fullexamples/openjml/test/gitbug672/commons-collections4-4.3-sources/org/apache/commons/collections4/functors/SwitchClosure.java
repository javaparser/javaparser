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
import java.util.Map;

import org.apache.commons.collections4.Closure;
import org.apache.commons.collections4.Predicate;

/**
 * Closure implementation calls the closure whose predicate returns true,
 * like a switch statement.
 *
 * @since 3.0
 */
public class SwitchClosure<E> implements Closure<E>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 3518477308466486130L;

    /** The tests to consider */
    private final Predicate<? super E>[] iPredicates;
    /** The matching closures to call */
    private final Closure<? super E>[] iClosures;
    /** The default closure to call if no tests match */
    private final Closure<? super E> iDefault;

    /**
     * Factory method that performs validation and copies the parameter arrays.
     *
     * @param <E> the type that the closure acts on
     * @param predicates  array of predicates, cloned, no nulls
     * @param closures  matching array of closures, cloned, no nulls
     * @param defaultClosure  the closure to use if no match, null means nop
     * @return the <code>chained</code> closure
     * @throws NullPointerException if array is null
     * @throws NullPointerException if any element in the array is null
     * @throws IllegalArgumentException if the array lengths of predicates and closures do not match
     */
    @SuppressWarnings("unchecked")
    public static <E> Closure<E> switchClosure(final Predicate<? super E>[] predicates,
                                               final Closure<? super E>[] closures,
                                               final Closure<? super E> defaultClosure) {
        FunctorUtils.validate(predicates);
        FunctorUtils.validate(closures);
        if (predicates.length != closures.length) {
            throw new IllegalArgumentException("The predicate and closure arrays must be the same size");
        }
        if (predicates.length == 0) {
            return (Closure<E>) (defaultClosure == null ? NOPClosure.<E>nopClosure(): defaultClosure);
        }
        return new SwitchClosure<>(predicates, closures, defaultClosure);
    }

    /**
     * Create a new Closure that calls one of the closures depending
     * on the predicates.
     * <p>
     * The Map consists of Predicate keys and Closure values. A closure
     * is called if its matching predicate returns true. Each predicate is evaluated
     * until one returns true. If no predicates evaluate to true, the default
     * closure is called. The default closure is set in the map with a
     * null key. The ordering is that of the iterator() method on the entryset
     * collection of the map.
     *
     * @param <E> the type that the closure acts on
     * @param predicatesAndClosures  a map of predicates to closures
     * @return the <code>switch</code> closure
     * @throws NullPointerException if the map is null
     * @throws NullPointerException if any closure in the map is null
     * @throws ClassCastException  if the map elements are of the wrong type
     */
    @SuppressWarnings("unchecked")
    public static <E> Closure<E> switchClosure(final Map<Predicate<E>, Closure<E>> predicatesAndClosures) {
        if (predicatesAndClosures == null) {
            throw new NullPointerException("The predicate and closure map must not be null");
        }
        // convert to array like this to guarantee iterator() ordering
        final Closure<? super E> defaultClosure = predicatesAndClosures.remove(null);
        final int size = predicatesAndClosures.size();
        if (size == 0) {
            return (Closure<E>) (defaultClosure == null ? NOPClosure.<E>nopClosure() : defaultClosure);
        }
        final Closure<E>[] closures = new Closure[size];
        final Predicate<E>[] preds = new Predicate[size];
        int i = 0;
        for (final Map.Entry<Predicate<E>, Closure<E>> entry : predicatesAndClosures.entrySet()) {
            preds[i] = entry.getKey();
            closures[i] = entry.getValue();
            i++;
        }
        return new SwitchClosure<>(false, preds, closures, defaultClosure);
    }

    /**
     * Hidden constructor for the use by the static factory methods.
     *
     * @param clone  if {@code true} the input arguments will be cloned
     * @param predicates  array of predicates, no nulls
     * @param closures  matching array of closures, no nulls
     * @param defaultClosure  the closure to use if no match, null means nop
     */
    @SuppressWarnings("unchecked")
    private SwitchClosure(final boolean clone, final Predicate<? super E>[] predicates,
                          final Closure<? super E>[] closures, final Closure<? super E> defaultClosure) {
        super();
        iPredicates = clone ? FunctorUtils.copy(predicates) : predicates;
        iClosures = clone ? FunctorUtils.copy(closures) : closures;
        iDefault = (Closure<? super E>) (defaultClosure == null ? NOPClosure.<E>nopClosure() : defaultClosure);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>switchClosure</code> if you want that.
     *
     * @param predicates  array of predicates, cloned, no nulls
     * @param closures  matching array of closures, cloned, no nulls
     * @param defaultClosure  the closure to use if no match, null means nop
     */
    public SwitchClosure(final Predicate<? super E>[] predicates, final Closure<? super E>[] closures,
                         final Closure<? super E> defaultClosure) {
        this(true, predicates, closures, defaultClosure);
    }

    /**
     * Executes the closure whose matching predicate returns true
     *
     * @param input  the input object
     */
    @Override
    public void execute(final E input) {
        for (int i = 0; i < iPredicates.length; i++) {
            if (iPredicates[i].evaluate(input) == true) {
                iClosures[i].execute(input);
                return;
            }
        }
        iDefault.execute(input);
    }

    /**
     * Gets the predicates.
     *
     * @return a copy of the predicates
     * @since 3.1
     */
    public Predicate<? super E>[] getPredicates() {
        return FunctorUtils.<E>copy(iPredicates);
    }

    /**
     * Gets the closures.
     *
     * @return a copy of the closures
     * @since 3.1
     */
    public Closure<? super E>[] getClosures() {
        return FunctorUtils.<E>copy(iClosures);
    }

    /**
     * Gets the default closure.
     *
     * @return the default closure
     * @since 3.1
     */
    public Closure<? super E> getDefaultClosure() {
        return iDefault;
    }

}
