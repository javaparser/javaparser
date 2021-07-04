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

import org.apache.commons.collections4.Factory;
import org.apache.commons.collections4.FunctorException;

/**
 * Factory implementation that creates a new object instance by reflection.
 * <p>
 * <b>WARNING:</b> from v4.1 onwards this class will <b>not</b> be serializable anymore
 * in order to prevent potential remote code execution exploits. Please refer to
 * <a href="https://issues.apache.org/jira/browse/COLLECTIONS-580">COLLECTIONS-580</a>
 * for more details.
 *
 * @since 3.0
 */
public class InstantiateFactory<T> implements Factory<T> {

    /** The class to create */
    private final Class<T> iClassToInstantiate;
    /** The constructor parameter types */
    private final Class<?>[] iParamTypes;
    /** The constructor arguments */
    private final Object[] iArgs;
    /** The constructor */
    private transient Constructor<T> iConstructor = null;

    /**
     * Factory method that performs validation.
     *
     * @param <T>  the type the factory creates
     * @param classToInstantiate  the class to instantiate, not null
     * @param paramTypes  the constructor parameter types, cloned
     * @param args  the constructor arguments, cloned
     * @return a new instantiate factory
     * @throws NullPointerException if classToInstantiate is null
     * @throws IllegalArgumentException if paramTypes does not match args
     */
    public static <T> Factory<T> instantiateFactory(final Class<T> classToInstantiate,
                                                    final Class<?>[] paramTypes,
                                                    final Object[] args) {
        if (classToInstantiate == null) {
            throw new NullPointerException("Class to instantiate must not be null");
        }
        if (paramTypes == null && args != null
            || paramTypes != null && args == null
            || paramTypes != null && args != null && paramTypes.length != args.length) {
            throw new IllegalArgumentException("Parameter types must match the arguments");
        }

        if (paramTypes == null || paramTypes.length == 0) {
            return new InstantiateFactory<>(classToInstantiate);
        }
        return new InstantiateFactory<>(classToInstantiate, paramTypes, args);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>instantiateFactory</code> if you want that.
     *
     * @param classToInstantiate  the class to instantiate
     */
    public InstantiateFactory(final Class<T> classToInstantiate) {
        super();
        iClassToInstantiate = classToInstantiate;
        iParamTypes = null;
        iArgs = null;
        findConstructor();
    }

    /**
     * Constructor that performs no validation.
     * Use <code>instantiateFactory</code> if you want that.
     *
     * @param classToInstantiate  the class to instantiate
     * @param paramTypes  the constructor parameter types, cloned
     * @param args  the constructor arguments, cloned
     */
    public InstantiateFactory(final Class<T> classToInstantiate, final Class<?>[] paramTypes, final Object[] args) {
        super();
        iClassToInstantiate = classToInstantiate;
        iParamTypes = paramTypes.clone();
        iArgs = args.clone();
        findConstructor();
    }

    /**
     * Find the Constructor for the class specified.
     */
    private void findConstructor() {
        try {
            iConstructor = iClassToInstantiate.getConstructor(iParamTypes);
        } catch (final NoSuchMethodException ex) {
            throw new IllegalArgumentException("InstantiateFactory: The constructor must exist and be public ");
        }
    }

    /**
     * Creates an object using the stored constructor.
     *
     * @return the new object
     */
    @Override
    public T create() {
        // needed for post-serialization
        if (iConstructor == null) {
            findConstructor();
        }

        try {
            return iConstructor.newInstance(iArgs);
        } catch (final InstantiationException ex) {
            throw new FunctorException("InstantiateFactory: InstantiationException", ex);
        } catch (final IllegalAccessException ex) {
            throw new FunctorException("InstantiateFactory: Constructor must be public", ex);
        } catch (final InvocationTargetException ex) {
            throw new FunctorException("InstantiateFactory: Constructor threw an exception", ex);
        }
    }

}
