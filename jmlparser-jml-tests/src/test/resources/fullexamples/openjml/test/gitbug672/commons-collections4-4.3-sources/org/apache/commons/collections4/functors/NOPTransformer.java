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

import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that does nothing.
 *
 * @since 3.0
 */
public class NOPTransformer<T> implements Transformer<T, T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 2133891748318574490L;

    /** Singleton predicate instance */
    @SuppressWarnings("rawtypes")
    public static final Transformer INSTANCE = new NOPTransformer<>();

    /**
     * Factory returning the singleton instance.
     *
     * @param <T>  the input/output type
     * @return the singleton instance
     * @since 3.1
     */
    @SuppressWarnings("unchecked")
    public static <T> Transformer<T, T> nopTransformer() {
        return INSTANCE;
    }

    /**
     * Constructor.
     */
    private NOPTransformer() {
        super();
    }

    /**
     * Transforms the input to result by doing nothing.
     *
     * @param input  the input object to transform
     * @return the transformed result which is the input
     */
    @Override
    public T transform(final T input) {
        return input;
    }

    private Object readResolve() {
        return INSTANCE;
    }

}
