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

import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;

import org.apache.commons.collections4.Factory;
import org.apache.commons.collections4.FunctorException;

/**
 * Factory implementation that creates a new instance each time based on a prototype.
 * <p>
 * <b>WARNING:</b> from v4.1 onwards {@link Factory} instances returned by
 * {@link #prototypeFactory(Object)} will <b>not</b> be serializable anymore in order
 * to prevent potential remote code execution exploits. Please refer to
 * <a href="https://issues.apache.org/jira/browse/COLLECTIONS-580">COLLECTIONS-580</a>
 * for more details.
 *
 * @since 3.0
 */
public class PrototypeFactory {

    /**
     * Factory method that performs validation.
     * <p>
     * Creates a Factory that will return a clone of the same prototype object
     * each time the factory is used. The prototype will be cloned using one of these
     * techniques (in order):
     * </p>
     *
     * <ul>
     * <li>public clone method</li>
     * <li>public copy constructor</li>
     * <li>serialization clone</li>
     * </ul>
     *
     * @param <T>  the type the factory creates
     * @param prototype  the object to clone each time in the factory
     * @return the <code>prototype</code> factory, or a {@link ConstantFactory#NULL_INSTANCE} if
     * the {@code prototype} is {@code null}
     * @throws IllegalArgumentException if the prototype cannot be cloned
     */
    @SuppressWarnings("unchecked")
    public static <T> Factory<T> prototypeFactory(final T prototype) {
        if (prototype == null) {
            return ConstantFactory.<T>constantFactory(null);
        }
        try {
            final Method method = prototype.getClass().getMethod("clone", (Class[]) null);
            return new PrototypeCloneFactory<>(prototype, method);

        } catch (final NoSuchMethodException ex) {
            try {
                prototype.getClass().getConstructor(new Class<?>[] { prototype.getClass() });
                return new InstantiateFactory<>(
                    (Class<T>) prototype.getClass(),
                    new Class<?>[] { prototype.getClass() },
                    new Object[] { prototype });
            } catch (final NoSuchMethodException ex2) {
                if (prototype instanceof Serializable) {
                    return (Factory<T>) new PrototypeSerializationFactory<>((Serializable) prototype);
                }
            }
        }
        throw new IllegalArgumentException("The prototype must be cloneable via a public clone method");
    }

    /**
     * Restricted constructor.
     */
    private PrototypeFactory() {
        super();
    }

    // PrototypeCloneFactory
    //-----------------------------------------------------------------------
    /**
     * PrototypeCloneFactory creates objects by copying a prototype using the clone method.
     */
    static class PrototypeCloneFactory<T> implements Factory<T> {

        /** The object to clone each time */
        private final T iPrototype;
        /** The method used to clone */
        private transient Method iCloneMethod;

        /**
         * Constructor to store prototype.
         */
        private PrototypeCloneFactory(final T prototype, final Method method) {
            super();
            iPrototype = prototype;
            iCloneMethod = method;
        }

        /**
         * Find the Clone method for the class specified.
         */
        private void findCloneMethod() {
            try {
                iCloneMethod = iPrototype.getClass().getMethod("clone", (Class[]) null);
            } catch (final NoSuchMethodException ex) {
                throw new IllegalArgumentException("PrototypeCloneFactory: The clone method must exist and be public ");
            }
        }

        /**
         * Creates an object by calling the clone method.
         *
         * @return the new object
         */
        @Override
        @SuppressWarnings("unchecked")
        public T create() {
            // needed for post-serialization
            if (iCloneMethod == null) {
                findCloneMethod();
            }

            try {
                return (T) iCloneMethod.invoke(iPrototype, (Object[]) null);
            } catch (final IllegalAccessException ex) {
                throw new FunctorException("PrototypeCloneFactory: Clone method must be public", ex);
            } catch (final InvocationTargetException ex) {
                throw new FunctorException("PrototypeCloneFactory: Clone method threw an exception", ex);
            }
        }
    }

    // PrototypeSerializationFactory
    //-----------------------------------------------------------------------
    /**
     * PrototypeSerializationFactory creates objects by cloning a prototype using serialization.
     */
    static class PrototypeSerializationFactory<T extends Serializable> implements Factory<T> {

        /** The object to clone via serialization each time */
        private final T iPrototype;

        /**
         * Constructor to store prototype
         */
        private PrototypeSerializationFactory(final T prototype) {
            super();
            iPrototype = prototype;
        }

        /**
         * Creates an object using serialization.
         *
         * @return the new object
         */
        @Override
        @SuppressWarnings("unchecked")
        public T create() {
            final ByteArrayOutputStream baos = new ByteArrayOutputStream(512);
            ByteArrayInputStream bais = null;
            try {
                final ObjectOutputStream out = new ObjectOutputStream(baos);
                out.writeObject(iPrototype);

                bais = new ByteArrayInputStream(baos.toByteArray());
                final ObjectInputStream in = new ObjectInputStream(bais);
                return (T) in.readObject();

            } catch (final ClassNotFoundException ex) {
                throw new FunctorException(ex);
            } catch (final IOException ex) {
                throw new FunctorException(ex);
            } finally {
                try {
                    if (bais != null) {
                        bais.close();
                    }
                } catch (final IOException ex) { //NOPMD
                    // ignore
                }
                try {
                    baos.close();
                } catch (final IOException ex) { //NOPMD
                    // ignore
                }
            }
        }
    }

}
