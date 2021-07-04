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
import java.util.Map;

import org.apache.commons.collections4.functors.ChainedClosure;
import org.apache.commons.collections4.functors.EqualPredicate;
import org.apache.commons.collections4.functors.ExceptionClosure;
import org.apache.commons.collections4.functors.ForClosure;
import org.apache.commons.collections4.functors.IfClosure;
import org.apache.commons.collections4.functors.InvokerTransformer;
import org.apache.commons.collections4.functors.NOPClosure;
import org.apache.commons.collections4.functors.SwitchClosure;
import org.apache.commons.collections4.functors.TransformerClosure;
import org.apache.commons.collections4.functors.WhileClosure;

/**
 * <code>ClosureUtils</code> provides reference implementations and utilities
 * for the Closure functor interface. The supplied closures are:
 * <ul>
 * <li>Invoker - invokes a method on the input object
 * <li>For - repeatedly calls a closure for a fixed number of times
 * <li>While - repeatedly calls a closure while a predicate is true
 * <li>Chained - chains two or more closures together
 * <li>If - calls one closure or another based on a predicate
 * <li>Switch - calls one closure based on one or more predicates
 * <li>SwitchMap - calls one closure looked up from a Map
 * <li>Transformer - wraps a Transformer as a Closure
 * <li>NOP - does nothing
 * <li>Exception - always throws an exception
 * </ul>
 * <p>
 * Since v4.1 only closures which are considered to be safe are
 * Serializable. Closures considered to be unsafe for serialization are:
 * <ul>
 * <li>Invoker
 * <li>For
 * <li>While
 * </ul>
 *
 * @since 3.0
 */
public class ClosureUtils {

    /**
     * This class is not normally instantiated.
     */
    private ClosureUtils() {}

    /**
     * Gets a Closure that always throws an exception.
     * This could be useful during testing as a placeholder.
     *
     * @see org.apache.commons.collections4.functors.ExceptionClosure
     *
     * @param <E>  the type that the closure acts on
     * @return the closure
     */
    public static <E> Closure<E> exceptionClosure() {
        return ExceptionClosure.<E>exceptionClosure();
    }

    /**
     * Gets a Closure that will do nothing.
     * This could be useful during testing as a placeholder.
     *
     * @see org.apache.commons.collections4.functors.NOPClosure
     *
     * @param <E>  the type that the closure acts on
     * @return the closure
     */
    public static <E> Closure<E> nopClosure() {
        return NOPClosure.<E>nopClosure();
    }

    /**
     * Creates a Closure that calls a Transformer each time it is called.
     * The transformer will be called using the closure's input object.
     * The transformer's result will be ignored.
     *
     * @see org.apache.commons.collections4.functors.TransformerClosure
     *
     * @param <E>  the type that the closure acts on
     * @param transformer  the transformer to run each time in the closure, null means nop
     * @return the closure
     */
    public static <E> Closure<E> asClosure(final Transformer<? super E, ?> transformer) {
        return TransformerClosure.transformerClosure(transformer);
    }

    /**
     * Creates a Closure that will call the closure <code>count</code> times.
     * <p>
     * A null closure or zero count returns the <code>NOPClosure</code>.
     *
     * @see org.apache.commons.collections4.functors.ForClosure
     *
     * @param <E>  the type that the closure acts on
     * @param count  the number of times to loop
     * @param closure  the closure to call repeatedly
     * @return the <code>for</code> closure
     */
    public static <E> Closure<E> forClosure(final int count, final Closure<? super E> closure) {
        return ForClosure.forClosure(count, closure);
    }

    /**
     * Creates a Closure that will call the closure repeatedly until the
     * predicate returns false.
     *
     * @see org.apache.commons.collections4.functors.WhileClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicate  the predicate to use as an end of loop test, not null
     * @param closure  the closure to call repeatedly, not null
     * @return the <code>while</code> closure
     * @throws NullPointerException if either argument is null
     */
    public static <E> Closure<E> whileClosure(final Predicate<? super E> predicate, final Closure<? super E> closure) {
        return WhileClosure.<E>whileClosure(predicate, closure, false);
    }

    /**
     * Creates a Closure that will call the closure once and then repeatedly
     * until the predicate returns false.
     *
     * @see org.apache.commons.collections4.functors.WhileClosure
     *
     * @param <E>  the type that the closure acts on
     * @param closure  the closure to call repeatedly, not null
     * @param predicate  the predicate to use as an end of loop test, not null
     * @return the <code>do-while</code> closure
     * @throws NullPointerException if either argument is null
     */
    public static <E> Closure<E> doWhileClosure(final Closure<? super E> closure,
                                                final Predicate<? super E> predicate) {
        return WhileClosure.<E>whileClosure(predicate, closure, true);
    }

    /**
     * Creates a Closure that will invoke a specific method on the closure's
     * input object by reflection.
     *
     * @see org.apache.commons.collections4.functors.InvokerTransformer
     * @see org.apache.commons.collections4.functors.TransformerClosure
     *
     * @param <E>  the type that the closure acts on
     * @param methodName  the name of the method
     * @return the <code>invoker</code> closure
     * @throws NullPointerException if the method name is null
     */
    public static <E> Closure<E> invokerClosure(final String methodName) {
        // reuse transformer as it has caching - this is lazy really, should have inner class here
        return asClosure(InvokerTransformer.<E, Object>invokerTransformer(methodName));
    }

    /**
     * Creates a Closure that will invoke a specific method on the closure's
     * input object by reflection.
     *
     * @see org.apache.commons.collections4.functors.InvokerTransformer
     * @see org.apache.commons.collections4.functors.TransformerClosure
     *
     * @param <E>  the type that the closure acts on
     * @param methodName  the name of the method
     * @param paramTypes  the parameter types
     * @param args  the arguments
     * @return the <code>invoker</code> closure
     * @throws NullPointerException if the method name is null
     * @throws IllegalArgumentException if the paramTypes and args don't match
     */
    public static <E> Closure<E> invokerClosure(final String methodName, final Class<?>[] paramTypes,
                                                final Object[] args) {
        // reuse transformer as it has caching - this is lazy really, should have inner class here
        return asClosure(InvokerTransformer.<E, Object>invokerTransformer(methodName, paramTypes, args));
    }

    /**
     * Create a new Closure that calls each closure in turn, passing the
     * result into the next closure.
     *
     * @see org.apache.commons.collections4.functors.ChainedClosure
     *
     * @param <E>  the type that the closure acts on
     * @param closures  an array of closures to chain
     * @return the <code>chained</code> closure
     * @throws NullPointerException if the closures array is null
     * @throws NullPointerException if any closure in the array is null
     */
    public static <E> Closure<E> chainedClosure(final Closure<? super E>... closures) {
        return ChainedClosure.chainedClosure(closures);
    }

    /**
     * Create a new Closure that calls each closure in turn, passing the
     * result into the next closure. The ordering is that of the iterator()
     * method on the collection.
     *
     * @see org.apache.commons.collections4.functors.ChainedClosure
     *
     * @param <E>  the type that the closure acts on
     * @param closures  a collection of closures to chain
     * @return the <code>chained</code> closure
     * @throws NullPointerException if the closures collection is null
     * @throws NullPointerException if any closure in the collection is null
     * @throws IllegalArgumentException if the closures collection is empty
     */
    public static <E> Closure<E> chainedClosure(final Collection<? extends Closure<? super E>> closures) {
        return ChainedClosure.chainedClosure(closures);
    }

    /**
     * Create a new Closure that calls another closure based on the
     * result of the specified predicate.
     *
     * @see org.apache.commons.collections4.functors.IfClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicate  the validating predicate
     * @param trueClosure  the closure called if the predicate is true
     * @return the <code>if</code> closure
     * @throws NullPointerException if the predicate or closure is null
     * @since 3.2
     */
    public static <E> Closure<E> ifClosure(final Predicate<? super E> predicate,
                                           final Closure<? super E> trueClosure) {
        return IfClosure.<E>ifClosure(predicate, trueClosure);
    }

    /**
     * Create a new Closure that calls one of two closures depending
     * on the specified predicate.
     *
     * @see org.apache.commons.collections4.functors.IfClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicate  the predicate to switch on
     * @param trueClosure  the closure called if the predicate is true
     * @param falseClosure  the closure called if the predicate is false
     * @return the <code>switch</code> closure
     * @throws NullPointerException if the predicate or either closure is null
     */
    public static <E> Closure<E> ifClosure(final Predicate<? super E> predicate,
                                           final Closure<? super E> trueClosure,
                                           final Closure<? super E> falseClosure) {
        return IfClosure.<E>ifClosure(predicate, trueClosure, falseClosure);
    }

    /**
     * Create a new Closure that calls one of the closures depending
     * on the predicates.
     * <p>
     * The closure at array location 0 is called if the predicate at array
     * location 0 returned true. Each predicate is evaluated
     * until one returns true.
     *
     * @see org.apache.commons.collections4.functors.SwitchClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicates  an array of predicates to check, not null
     * @param closures  an array of closures to call, not null
     * @return the <code>switch</code> closure
     * @throws NullPointerException if the either array is null
     * @throws NullPointerException if any element in the arrays is null
     * @throws IllegalArgumentException if the arrays have different sizes
     */
    public static <E> Closure<E> switchClosure(final Predicate<? super E>[] predicates,
                                               final Closure<? super E>[] closures) {
        return SwitchClosure.<E>switchClosure(predicates, closures, null);
    }

    /**
     * Create a new Closure that calls one of the closures depending
     * on the predicates.
     * <p>
     * The closure at array location 0 is called if the predicate at array
     * location 0 returned true. Each predicate is evaluated
     * until one returns true. If no predicates evaluate to true, the default
     * closure is called.
     *
     * @see org.apache.commons.collections4.functors.SwitchClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicates  an array of predicates to check, not null
     * @param closures  an array of closures to call, not null
     * @param defaultClosure  the default to call if no predicate matches
     * @return the <code>switch</code> closure
     * @throws NullPointerException if the either array is null
     * @throws NullPointerException if any element in the arrays is null
     * @throws IllegalArgumentException if the arrays are different sizes
     */
    public static <E> Closure<E> switchClosure(final Predicate<? super E>[] predicates,
                                               final Closure<? super E>[] closures,
                                               final Closure<? super E> defaultClosure) {
        return SwitchClosure.<E>switchClosure(predicates, closures, defaultClosure);
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
     * @see org.apache.commons.collections4.functors.SwitchClosure
     *
     * @param <E>  the type that the closure acts on
     * @param predicatesAndClosures  a map of predicates to closures
     * @return the <code>switch</code> closure
     * @throws NullPointerException if the map is null
     * @throws NullPointerException if any closure in the map is null
     * @throws IllegalArgumentException if the map is empty
     * @throws ClassCastException  if the map elements are of the wrong type
     */
    public static <E> Closure<E> switchClosure(final Map<Predicate<E>, Closure<E>> predicatesAndClosures) {
        return SwitchClosure.switchClosure(predicatesAndClosures);
    }

    /**
     * Create a new Closure that uses the input object as a key to find the
     * closure to call.
     * <p>
     * The Map consists of object keys and Closure values. A closure
     * is called if the input object equals the key. If there is no match, the
     * default closure is called. The default closure is set in the map
     * using a null key.
     *
     * @see org.apache.commons.collections4.functors.SwitchClosure
     *
     * @param <E>  the type that the closure acts on
     * @param objectsAndClosures  a map of objects to closures
     * @return the closure
     * @throws NullPointerException if the map is null
     * @throws NullPointerException if any closure in the map is null
     * @throws IllegalArgumentException if the map is empty
     */
    @SuppressWarnings("unchecked")
    public static <E> Closure<E> switchMapClosure(final Map<? extends E, Closure<E>> objectsAndClosures) {
        if (objectsAndClosures == null) {
            throw new NullPointerException("The object and closure map must not be null");
        }
        final Closure<? super E> def = objectsAndClosures.remove(null);
        final int size = objectsAndClosures.size();
        final Closure<? super E>[] trs = new Closure[size];
        final Predicate<E>[] preds = new Predicate[size];
        int i = 0;
        for (final Map.Entry<? extends E, Closure<E>> entry : objectsAndClosures.entrySet()) {
            preds[i] = EqualPredicate.<E>equalPredicate(entry.getKey());
            trs[i] = entry.getValue();
            i++;
        }
        return ClosureUtils.<E>switchClosure(preds, trs, def);
    }

}
