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

import org.apache.commons.collections4.FunctorException;
import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that always throws an exception.
 *
 * @since 3.0
 */
public final class ExceptionTransformer<I, O> implements Transformer<I, O>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 7179106032121985545L;

    /** Singleton predicate instance */
    @SuppressWarnings("rawtypes") // the static instance works for all types
    public static final Transformer INSTANCE = new ExceptionTransformer<>();

    /**
     * Factory returning the singleton instance.
     *
     * @param <I>  the input type
     * @param <O>  the output type
     * @return the singleton instance
     * @since 3.1
     */
    @SuppressWarnings("unchecked") // the static instance works for all types
    public static <I, O> Transformer<I, O> exceptionTransformer() {
        return INSTANCE;
    }

    /**
     * Restricted constructor.
     */
    private ExceptionTransformer() {
        super();
    }

    /**
     * Transforms the input to result by cloning it.
     *
     * @param input  the input object to transform
     * @return never
     * @throws FunctorException always
     */
    @Override
    public O transform(final I input) {
        throw new FunctorException("ExceptionTransformer invoked");
    }

    private Object readResolve() {
        return INSTANCE;
    }

}
