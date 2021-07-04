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

import org.apache.commons.collections4.functors.AllPredicate;
import org.apache.commons.collections4.functors.AndPredicate;
import org.apache.commons.collections4.functors.AnyPredicate;
import org.apache.commons.collections4.functors.EqualPredicate;
import org.apache.commons.collections4.functors.ExceptionPredicate;
import org.apache.commons.collections4.functors.FalsePredicate;
import org.apache.commons.collections4.functors.IdentityPredicate;
import org.apache.commons.collections4.functors.InstanceofPredicate;
import org.apache.commons.collections4.functors.InvokerTransformer;
import org.apache.commons.collections4.functors.NonePredicate;
import org.apache.commons.collections4.functors.NotNullPredicate;
import org.apache.commons.collections4.functors.NotPredicate;
import org.apache.commons.collections4.functors.NullIsExceptionPredicate;
import org.apache.commons.collections4.functors.NullIsFalsePredicate;
import org.apache.commons.collections4.functors.NullIsTruePredicate;
import org.apache.commons.collections4.functors.NullPredicate;
import org.apache.commons.collections4.functors.OnePredicate;
import org.apache.commons.collections4.functors.OrPredicate;
import org.apache.commons.collections4.functors.TransformedPredicate;
import org.apache.commons.collections4.functors.TransformerPredicate;
import org.apache.commons.collections4.functors.TruePredicate;
import org.apache.commons.collections4.functors.UniquePredicate;

/**
 * <code>PredicateUtils</code> provides reference implementations and utilities
 * for the Predicate functor interface. The supplied predicates are:
 * <ul>
 * <li>Invoker - returns the result of a method call on the input object
 * <li>InstanceOf - true if the object is an instanceof a class
 * <li>Equal - true if the object equals() a specified object
 * <li>Identity - true if the object == a specified object
 * <li>Null - true if the object is null
 * <li>NotNull - true if the object is not null
 * <li>Unique - true if the object has not already been evaluated
 * <li>And/All - true if all of the predicates are true
 * <li>Or/Any - true if any of the predicates is true
 * <li>Either/One - true if only one of the predicate is true
 * <li>Neither/None - true if none of the predicates are true
 * <li>Not - true if the predicate is false, and vice versa
 * <li>Transformer - wraps a Transformer as a Predicate
 * <li>True - always return true
 * <li>False - always return false
 * <li>Exception - always throws an exception
 * <li>NullIsException/NullIsFalse/NullIsTrue - check for null input
 * <li>Transformed - transforms the input before calling the predicate
 * </ul>
 * All the supplied predicates are Serializable.
 *
 * @since 3.0
 */
public class PredicateUtils {

    /**
     * This class is not normally instantiated.
     */
    private PredicateUtils() {}

    // Simple predicates
    //-----------------------------------------------------------------------------

    /**
     * Gets a Predicate that always throws an exception.
     * This could be useful during testing as a placeholder.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see ExceptionPredicate
     */
    public static <T> Predicate<T> exceptionPredicate() {
        return ExceptionPredicate.exceptionPredicate();
    }

    /**
     * Gets a Predicate that always returns true.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see TruePredicate
     */
    public static <T> Predicate<T> truePredicate() {
        return TruePredicate.truePredicate();
    }

    /**
     * Gets a Predicate that always returns false.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see FalsePredicate
     */
    public static <T> Predicate<T> falsePredicate() {
        return FalsePredicate.falsePredicate();
    }

    /**
     * Gets a Predicate that checks if the input object passed in is null.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see NullPredicate
     */
    public static <T> Predicate<T> nullPredicate() {
        return NullPredicate.nullPredicate();
    }

    /**
     * Gets a Predicate that checks if the input object passed in is not null.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see NotNullPredicate
     */
    public static <T> Predicate<T> notNullPredicate() {
        return NotNullPredicate.notNullPredicate();
    }

    /**
     * Creates a Predicate that checks if the input object is equal to the
     * specified object using equals().
     *
     * @param <T>  the type that the predicate queries
     * @param value  the value to compare against
     * @return the predicate
     * @see EqualPredicate
     */
    public static <T> Predicate<T> equalPredicate(final T value) {
        return EqualPredicate.equalPredicate(value);
    }

    /**
     * Creates a Predicate that checks if the input object is equal to the
     * specified object by identity.
     *
     * @param <T>  the type that the predicate queries
     * @param value  the value to compare against
     * @return the predicate
     * @see IdentityPredicate
     */
    public static <T> Predicate<T> identityPredicate(final T value) {
        return IdentityPredicate.identityPredicate(value);
    }

    /**
     * Creates a Predicate that checks if the object passed in is of
     * a particular type, using instanceof. A <code>null</code> input
     * object will return <code>false</code>.
     *
     * @param type  the type to check for, may not be null
     * @return the predicate
     * @throws NullPointerException if the class is null
     * @see InstanceofPredicate
     */
    public static Predicate<Object> instanceofPredicate(final Class<?> type) {
        return InstanceofPredicate.instanceOfPredicate(type);
    }

    /**
     * Creates a Predicate that returns true the first time an object is
     * encountered, and false if the same object is received
     * again. The comparison is by equals(). A <code>null</code> input object
     * is accepted and will return true the first time, and false subsequently
     * as well.
     *
     * @param <T>  the type that the predicate queries
     * @return the predicate
     * @see UniquePredicate
     */
    public static <T> Predicate<T> uniquePredicate() {
        // must return new instance each time
        return UniquePredicate.uniquePredicate();
    }

    /**
     * Creates a Predicate that invokes a method on the input object.
     * The method must return either a boolean or a non-null Boolean,
     * and have no parameters. If the input object is null, a
     * PredicateException is thrown.
     * <p>
     * For example, <code>PredicateUtils.invokerPredicate("isEmpty");</code>
     * will call the <code>isEmpty</code> method on the input object to
     * determine the predicate result.
     *
     * @param <T>  the type that the predicate queries
     * @param methodName  the method name to call on the input object, may not be null
     * @return the predicate
     * @throws NullPointerException if the methodName is null.
     * @see InvokerTransformer
     * @see TransformerPredicate
     */
    public static <T> Predicate<T> invokerPredicate(final String methodName) {
        // reuse transformer as it has caching - this is lazy really, should have inner class here
        return asPredicate(InvokerTransformer.<Object, Boolean>invokerTransformer(methodName));
    }

    /**
     * Creates a Predicate that invokes a method on the input object.
     * The method must return either a boolean or a non-null Boolean,
     * and have no parameters. If the input object is null, a
     * PredicateException is thrown.
     * <p>
     * For example, <code>PredicateUtils.invokerPredicate("isEmpty");</code>
     * will call the <code>isEmpty</code> method on the input object to
     * determine the predicate result.
     *
     * @param <T>  the type that the predicate queries
     * @param methodName  the method name to call on the input object, may not be null
     * @param paramTypes  the parameter types
     * @param args  the arguments
     * @return the predicate
     * @throws NullPointerException if the method name is null
     * @throws IllegalArgumentException if the paramTypes and args don't match
     * @see InvokerTransformer
     * @see TransformerPredicate
     */
    public static <T> Predicate<T> invokerPredicate(final String methodName, final Class<?>[] paramTypes,
                                                    final Object[] args) {
        // reuse transformer as it has caching - this is lazy really, should have inner class here
        return asPredicate(InvokerTransformer.<Object, Boolean>invokerTransformer(methodName, paramTypes, args));
    }

    // Boolean combinations
    //-----------------------------------------------------------------------------

    /**
     * Create a new Predicate that returns true only if both of the specified
     * predicates are true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate1  the first predicate, may not be null
     * @param predicate2  the second predicate, may not be null
     * @return the <code>and</code> predicate
     * @throws NullPointerException if either predicate is null
     * @see AndPredicate
     */
    public static <T> Predicate<T> andPredicate(final Predicate<? super T> predicate1,
                                                final Predicate<? super T> predicate2) {
        return AndPredicate.andPredicate(predicate1, predicate2);
    }

    /**
     * Create a new Predicate that returns true only if all of the specified
     * predicates are true.
     * If the array of predicates is empty, then this predicate returns true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  an array of predicates to check, may not be null
     * @return the <code>all</code> predicate
     * @throws NullPointerException if the predicates array is null
     * @throws NullPointerException if any predicate in the array is null
     * @see AllPredicate
     */
    public static <T> Predicate<T> allPredicate(final Predicate<? super T>... predicates) {
        return AllPredicate.allPredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true only if all of the specified
     * predicates are true. The predicates are checked in iterator order.
     * If the collection of predicates is empty, then this predicate returns true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  a collection of predicates to check, may not be null
     * @return the <code>all</code> predicate
     * @throws NullPointerException if the predicates collection is null
     * @throws NullPointerException if any predicate in the collection is null
     * @see AllPredicate
     */
    public static <T> Predicate<T> allPredicate(final Collection<? extends Predicate<? super T>> predicates) {
        return AllPredicate.allPredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if either of the specified
     * predicates are true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate1  the first predicate, may not be null
     * @param predicate2  the second predicate, may not be null
     * @return the <code>or</code> predicate
     * @throws NullPointerException if either predicate is null
     * @see OrPredicate
     */
    public static <T> Predicate<T> orPredicate(final Predicate<? super T> predicate1,
                                               final Predicate<? super T> predicate2) {
        return OrPredicate.orPredicate(predicate1, predicate2);
    }

    /**
     * Create a new Predicate that returns true if any of the specified
     * predicates are true.
     * If the array of predicates is empty, then this predicate returns false.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  an array of predicates to check, may not be null
     * @return the <code>any</code> predicate
     * @throws NullPointerException if the predicates array is null
     * @throws NullPointerException if any predicate in the array is null
     * @see AnyPredicate
     */
    public static <T> Predicate<T> anyPredicate(final Predicate<? super T>... predicates) {
        return AnyPredicate.anyPredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if any of the specified
     * predicates are true. The predicates are checked in iterator order.
     * If the collection of predicates is empty, then this predicate returns false.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  a collection of predicates to check, may not be null
     * @return the <code>any</code> predicate
     * @throws NullPointerException if the predicates collection is null
     * @throws NullPointerException if any predicate in the collection is null
     * @see AnyPredicate
     */
    public static <T> Predicate<T> anyPredicate(final Collection<? extends Predicate<? super T>> predicates) {
        return AnyPredicate.anyPredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if one, but not both, of the
     * specified predicates are true. XOR
     *
     * @param <T>  the type that the predicate queries
     * @param predicate1  the first predicate, may not be null
     * @param predicate2  the second predicate, may not be null
     * @return the <code>either</code> predicate
     * @throws NullPointerException if either predicate is null
     * @see OnePredicate
     */
    public static <T> Predicate<T> eitherPredicate(final Predicate<? super T> predicate1,
                                                   final Predicate<? super T> predicate2) {
        @SuppressWarnings("unchecked")
        final Predicate<T> onePredicate = PredicateUtils.onePredicate(predicate1, predicate2);
        return onePredicate;
    }

    /**
     * Create a new Predicate that returns true if only one of the specified
     * predicates are true.
     * If the array of predicates is empty, then this predicate returns false.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  an array of predicates to check, may not be null
     * @return the <code>one</code> predicate
     * @throws NullPointerException if the predicates array is null
     * @throws NullPointerException if any predicate in the array is null
     * @see OnePredicate
     */
    public static <T> Predicate<T> onePredicate(final Predicate<? super T>... predicates) {
        return OnePredicate.onePredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if only one of the specified
     * predicates are true. The predicates are checked in iterator order.
     * If the collection of predicates is empty, then this predicate returns false.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  a collection of predicates to check, may not be null
     * @return the <code>one</code> predicate
     * @throws NullPointerException if the predicates collection is null
     * @throws NullPointerException if any predicate in the collection is null
     * @see OnePredicate
     */
    public static <T> Predicate<T> onePredicate(final Collection<? extends Predicate<? super T>> predicates) {
        return OnePredicate.onePredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if neither of the specified
     * predicates are true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate1  the first predicate, may not be null
     * @param predicate2  the second predicate, may not be null
     * @return the <code>neither</code> predicate
     * @throws NullPointerException if either predicate is null
     * @see NonePredicate
     */
    public static <T> Predicate<T> neitherPredicate(final Predicate<? super T> predicate1,
                                                    final Predicate<? super T> predicate2) {
        @SuppressWarnings("unchecked")
        final Predicate<T> nonePredicate = PredicateUtils.nonePredicate(predicate1, predicate2);
        return nonePredicate;
    }

    /**
     * Create a new Predicate that returns true if none of the specified
     * predicates are true.
     * If the array of predicates is empty, then this predicate returns true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  an array of predicates to check, may not be null
     * @return the <code>none</code> predicate
     * @throws NullPointerException if the predicates array is null
     * @throws NullPointerException if any predicate in the array is null
     * @see NonePredicate
     */
    public static <T> Predicate<T> nonePredicate(final Predicate<? super T>... predicates) {
        return NonePredicate.nonePredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if none of the specified
     * predicates are true. The predicates are checked in iterator order.
     * If the collection of predicates is empty, then this predicate returns true.
     *
     * @param <T>  the type that the predicate queries
     * @param predicates  a collection of predicates to check, may not be null
     * @return the <code>none</code> predicate
     * @throws NullPointerException if the predicates collection is null
     * @throws NullPointerException if any predicate in the collection is null
     * @see NonePredicate
     */
    public static <T> Predicate<T> nonePredicate(final Collection<? extends Predicate<? super T>> predicates) {
        return NonePredicate.nonePredicate(predicates);
    }

    /**
     * Create a new Predicate that returns true if the specified predicate
     * returns false and vice versa.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate  the predicate to not
     * @return the <code>not</code> predicate
     * @throws NullPointerException if the predicate is null
     * @see NotPredicate
     */
    public static <T> Predicate<T> notPredicate(final Predicate<? super T> predicate) {
        return NotPredicate.notPredicate(predicate);
    }

    // Adaptors
    //-----------------------------------------------------------------------------

    /**
     * Create a new Predicate that wraps a Transformer. The Transformer must
     * return either Boolean.TRUE or Boolean.FALSE otherwise a PredicateException
     * will be thrown.
     *
     * @param <T>  the type that the predicate queries
     * @param transformer  the transformer to wrap, may not be null
     * @return the transformer wrapping predicate
     * @throws NullPointerException if the transformer is null
     * @see TransformerPredicate
     */
    public static <T> Predicate<T> asPredicate(final Transformer<? super T, Boolean> transformer) {
        return TransformerPredicate.transformerPredicate(transformer);
    }

    // Null handlers
    //-----------------------------------------------------------------------------

    /**
     * Gets a Predicate that throws an exception if the input object is null,
     * otherwise it calls the specified Predicate. This allows null handling
     * behaviour to be added to Predicates that don't support nulls.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate  the predicate to wrap, may not be null
     * @return the predicate
     * @throws NullPointerException if the predicate is null.
     * @see NullIsExceptionPredicate
     */
    public static <T> Predicate<T> nullIsExceptionPredicate(final Predicate<? super T> predicate){
        return NullIsExceptionPredicate.nullIsExceptionPredicate(predicate);
    }

    /**
     * Gets a Predicate that returns false if the input object is null, otherwise
     * it calls the specified Predicate. This allows null handling behaviour to
     * be added to Predicates that don't support nulls.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate  the predicate to wrap, may not be null
     * @return the predicate
     * @throws NullPointerException if the predicate is null.
     * @see NullIsFalsePredicate
     */
    public static <T> Predicate<T> nullIsFalsePredicate(final Predicate<? super T> predicate){
        return NullIsFalsePredicate.nullIsFalsePredicate(predicate);
    }

    /**
     * Gets a Predicate that returns true if the input object is null, otherwise
     * it calls the specified Predicate. This allows null handling behaviour to
     * be added to Predicates that don't support nulls.
     *
     * @param <T>  the type that the predicate queries
     * @param predicate  the predicate to wrap, may not be null
     * @return the predicate
     * @throws NullPointerException if the predicate is null.
     * @see NullIsTruePredicate
     */
    public static <T> Predicate<T> nullIsTruePredicate(final Predicate<? super T> predicate){
        return NullIsTruePredicate.nullIsTruePredicate(predicate);
    }

    // Transformed
    //-----------------------------------------------------------------------
    /**
     * Creates a predicate that transforms the input object before passing it
     * to the predicate.
     *
     * @param <T>  the type that the predicate queries
     * @param transformer  the transformer to call first
     * @param predicate  the predicate to call with the result of the transform
     * @return the predicate
     * @throws NullPointerException if the transformer or the predicate is null
     * @see TransformedPredicate
     * @since 3.1
     */
    public static <T> Predicate<T> transformedPredicate(
            final Transformer<? super T, ? extends T> transformer, final Predicate<? super T> predicate) {
        return TransformedPredicate.transformedPredicate(transformer, predicate);
    }

}
