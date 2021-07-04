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

import org.apache.commons.collections4.functors.ConstantFactory;
import org.apache.commons.collections4.functors.ExceptionFactory;
import org.apache.commons.collections4.functors.InstantiateFactory;
import org.apache.commons.collections4.functors.PrototypeFactory;

/**
 * <code>FactoryUtils</code> provides reference implementations and utilities
 * for the Factory functor interface. The supplied factories are:
 * <ul>
 * <li>Prototype - clones a specified object
 * <li>Instantiate - creates objects using reflection
 * <li>Constant - always returns the same object
 * <li>Null - always returns null
 * <li>Exception - always throws an exception
 * </ul>
 * <p>
 * Since v4.1 only factories which are considered to be safe are
 * Serializable. Factories considered to be unsafe for serialization are:
 * <ul>
 * <li>Prototype
 * <li>Instantiate
 * </ul>
 *
 * @since 3.0
 */
public class FactoryUtils {

    /**
     * This class is not normally instantiated.
     */
    private FactoryUtils() {}

    /**
     * Gets a Factory that always throws an exception.
     * This could be useful during testing as a placeholder.
     *
     * @see org.apache.commons.collections4.functors.ExceptionFactory
     *
     * @param <T> the type that the factory creates
     * @return the factory
     */
    public static <T> Factory<T> exceptionFactory() {
        return ExceptionFactory.<T>exceptionFactory();
    }

    /**
     * Gets a Factory that will return null each time the factory is used.
     * This could be useful during testing as a placeholder.
     *
     * @see org.apache.commons.collections4.functors.ConstantFactory
     * @param <T> the "type" of null object the factory should return.
     * @return the factory
     */
    public static <T> Factory<T> nullFactory() {
        return ConstantFactory.<T>constantFactory(null);
    }

    /**
     * Creates a Factory that will return the same object each time the factory
     * is used. No check is made that the object is immutable. In general, only
     * immutable objects should use the constant factory. Mutable objects should
     * use the prototype factory.
     *
     * @see org.apache.commons.collections4.functors.ConstantFactory
     *
     * @param <T> the type that the factory creates
     * @param constantToReturn  the constant object to return each time in the factory
     * @return the <code>constant</code> factory.
     */
    public static <T> Factory<T> constantFactory(final T constantToReturn) {
        return ConstantFactory.constantFactory(constantToReturn);
    }

    /**
     * Creates a Factory that will return a clone of the same prototype object
     * each time the factory is used. The prototype will be cloned using one of these
     * techniques (in order):
     *
     * <ul>
     * <li>public clone method</li>
     * <li>public copy constructor</li>
     * <li>serialization clone</li>
     * </ul>
     *
     * @see org.apache.commons.collections4.functors.PrototypeFactory
     *
     * @param <T> the type that the factory creates
     * @param prototype  the object to clone each time in the factory
     * @return the <code>prototype</code> factory, or a {@link ConstantFactory#NULL_INSTANCE} if
     * the {@code prototype} is {@code null}
     * @throws IllegalArgumentException if the prototype cannot be cloned
     */
    public static <T> Factory<T> prototypeFactory(final T prototype) {
        return PrototypeFactory.<T>prototypeFactory(prototype);
    }

    /**
     * Creates a Factory that can create objects of a specific type using
     * a no-args constructor.
     *
     * @see org.apache.commons.collections4.functors.InstantiateFactory
     *
     * @param <T> the type that the factory creates
     * @param classToInstantiate  the Class to instantiate each time in the factory
     * @return the <code>reflection</code> factory
     * @throws NullPointerException if the classToInstantiate is null
     */
    public static <T> Factory<T> instantiateFactory(final Class<T> classToInstantiate) {
        return InstantiateFactory.instantiateFactory(classToInstantiate, null, null);
    }

    /**
     * Creates a Factory that can create objects of a specific type using
     * the arguments specified to this method.
     *
     * @see org.apache.commons.collections4.functors.InstantiateFactory
     *
     * @param <T> the type that the factory creates
     * @param classToInstantiate  the Class to instantiate each time in the factory
     * @param paramTypes  parameter types for the constructor, can be null
     * @param args  the arguments to pass to the constructor, can be null
     * @return the <code>reflection</code> factory
     * @throws NullPointerException if the classToInstantiate is null
     * @throws IllegalArgumentException if the paramTypes and args don't match
     * @throws IllegalArgumentException if the constructor doesn't exist
     */
    public static <T> Factory<T> instantiateFactory(final Class<T> classToInstantiate, final Class<?>[] paramTypes,
                                                    final Object[] args) {
        return InstantiateFactory.instantiateFactory(classToInstantiate, paramTypes, args);
    }

}
