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

import org.apache.commons.collections4.Closure;
import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that calls a Closure using the input object
 * and then returns the input.
 *
 * @since 3.0
 */
public class ClosureTransformer<T> implements Transformer<T, T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 478466901448617286L;

    /** The closure to wrap */
    private final Closure<? super T> iClosure;

    /**
     * Factory method that performs validation.
     *
     * @param <T>  the type of the object to transform
     * @param closure  the closure to call, not null
     * @return the <code>closure</code> transformer
     * @throws NullPointerException if the closure is null
     */
    public static <T> Transformer<T, T> closureTransformer(final Closure<? super T> closure) {
        if (closure == null) {
            throw new NullPointerException("Closure must not be null");
        }
        return new ClosureTransformer<>(closure);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>closureTransformer</code> if you want that.
     *
     * @param closure  the closure to call, not null
     */
    public ClosureTransformer(final Closure<? super T> closure) {
        super();
        iClosure = closure;
    }

    /**
     * Transforms the input to result by executing a closure.
     *
     * @param input  the input object to transform
     * @return the transformed result
     */
    @Override
    public T transform(final T input) {
        iClosure.execute(input);
        return input;
    }

    /**
     * Gets the closure.
     *
     * @return the closure
     * @since 3.1
     */
    public Closure<? super T> getClosure() {
        return iClosure;
    }

}
