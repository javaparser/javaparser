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

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;

import org.apache.commons.collections4.FunctorException;
import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that creates a new object instance by reflection.
 * <p>
 * <b>WARNING:</b> from v4.1 onwards this class will <b>not</b> be serializable anymore
 * in order to prevent potential remote code execution exploits. Please refer to
 * <a href="https://issues.apache.org/jira/browse/COLLECTIONS-580">COLLECTIONS-580</a>
 * for more details.
 *
 * @since 3.0
 */
public class InstantiateTransformer<T> implements Transformer<Class<? extends T>, T> {

    /** Singleton instance that uses the no arg constructor */
    @SuppressWarnings("rawtypes")
    private static final Transformer NO_ARG_INSTANCE = new InstantiateTransformer<>();

    /** The constructor parameter types */
    private final Class<?>[] iParamTypes;
    /** The constructor arguments */
    private final Object[] iArgs;

    /**
     * Get a typed no-arg instance.
     *
     * @param <T>  the type of the objects to be created
     * @return Transformer&lt;Class&lt;? extends T&gt;, T&gt;
     */
    @SuppressWarnings("unchecked")
    public static <T> Transformer<Class<? extends T>, T> instantiateTransformer() {
        return NO_ARG_INSTANCE;
    }

    /**
     * Transformer method that performs validation.
     *
     * @param <T>  the type of the objects to be created
     * @param paramTypes  the constructor parameter types
     * @param args  the constructor arguments
     * @return an instantiate transformer
     * @throws IllegalArgumentException if paramTypes does not match args
     */
    public static <T> Transformer<Class<? extends T>, T> instantiateTransformer(final Class<?>[] paramTypes,
                                                                                final Object[] args) {
        if (((paramTypes == null) && (args != null))
            || ((paramTypes != null) && (args == null))
            || ((paramTypes != null) && (args != null) && (paramTypes.length != args.length))) {
            throw new IllegalArgumentException("Parameter types must match the arguments");
        }

        if (paramTypes == null || paramTypes.length == 0) {
            return new InstantiateTransformer<>();
        }
        return new InstantiateTransformer<>(paramTypes, args);
    }

    /**
     * Constructor for no arg instance.
     */
    private InstantiateTransformer() {
        super();
        iParamTypes = null;
        iArgs = null;
    }

    /**
     * Constructor that performs no validation.
     * Use <code>instantiateTransformer</code> if you want that.
     * <p>
     * Note: from 4.0, the input parameters will be cloned
     *
     * @param paramTypes  the constructor parameter types
     * @param args  the constructor arguments
     */
    public InstantiateTransformer(final Class<?>[] paramTypes, final Object[] args) {
        super();
        iParamTypes = paramTypes != null ? paramTypes.clone() : null;
        iArgs = args != null ? args.clone() : null;
    }

    /**
     * Transforms the input Class object to a result by instantiation.
     *
     * @param input  the input object to transform
     * @return the transformed result
     */
    @Override
    public T transform(final Class<? extends T> input) {
        try {
            if (input == null) {
                throw new FunctorException(
                    "InstantiateTransformer: Input object was not an instanceof Class, it was a null object");
            }
            final Constructor<? extends T> con = input.getConstructor(iParamTypes);
            return con.newInstance(iArgs);
        } catch (final NoSuchMethodException ex) {
            throw new FunctorException("InstantiateTransformer: The constructor must exist and be public ");
        } catch (final InstantiationException ex) {
            throw new FunctorException("InstantiateTransformer: InstantiationException", ex);
        } catch (final IllegalAccessException ex) {
            throw new FunctorException("InstantiateTransformer: Constructor must be public", ex);
        } catch (final InvocationTargetException ex) {
            throw new FunctorException("InstantiateTransformer: Constructor threw an exception", ex);
        }
    }

}
