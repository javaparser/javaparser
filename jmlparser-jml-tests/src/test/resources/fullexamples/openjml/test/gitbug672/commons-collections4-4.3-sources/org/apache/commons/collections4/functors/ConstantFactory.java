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

import org.apache.commons.collections4.Factory;

/**
 * Factory implementation that returns the same constant each time.
 * <p>
 * No check is made that the object is immutable. In general, only immutable
 * objects should use the constant factory. Mutable objects should
 * use the prototype factory.
 *
 * @since 3.0
 */
public class ConstantFactory<T> implements Factory<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = -3520677225766901240L;

    /** Returns null each time */
    @SuppressWarnings("rawtypes") // The null factory works for all object types
    public static final Factory NULL_INSTANCE = new ConstantFactory<>(null);

    /** The closures to call in turn */
    private final T iConstant;

    /**
     * Factory method that performs validation.
     *
     * @param <T>  the type of the constant
     * @param constantToReturn  the constant object to return each time in the factory
     * @return the <code>constant</code> factory.
     */
    @SuppressWarnings("unchecked") // The null factory works for all object types
    public static <T> Factory<T> constantFactory(final T constantToReturn) {
        if (constantToReturn == null) {
            return NULL_INSTANCE;
        }
        return new ConstantFactory<>(constantToReturn);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>constantFactory</code> if you want that.
     *
     * @param constantToReturn  the constant to return each time
     */
    public ConstantFactory(final T constantToReturn) {
        super();
        iConstant = constantToReturn;
    }

    /**
     * Always return constant.
     *
     * @return the stored constant value
     */
    @Override
    public T create() {
        return iConstant;
    }

    /**
     * Gets the constant.
     *
     * @return the constant
     * @since 3.1
     */
    public T getConstant() {
        return iConstant;
    }

}
