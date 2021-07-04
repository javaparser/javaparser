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

import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.Transformer;

/**
 * Predicate implementation that transforms the given object before invoking
 * another <code>Predicate</code>.
 *
 * @since 3.1
 */
public final class TransformedPredicate<T> implements PredicateDecorator<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = -5596090919668315834L;

    /** The transformer to call */
    private final Transformer<? super T, ? extends T> iTransformer;

    /** The predicate to call */
    private final Predicate<? super T> iPredicate;

    /**
     * Factory to create the predicate.
     *
     * @param <T> the type that the predicate queries
     * @param transformer  the transformer to call
     * @param predicate  the predicate to call with the result of the transform
     * @return the predicate
     * @throws NullPointerException if the transformer or the predicate is null
     */
    public static <T> Predicate<T> transformedPredicate(final Transformer<? super T, ? extends T> transformer,
                                                        final Predicate<? super T> predicate) {
        if (transformer == null) {
            throw new NullPointerException("The transformer to call must not be null");
        }
        if (predicate == null) {
            throw new NullPointerException("The predicate to call must not be null");
        }
        return new TransformedPredicate<>(transformer, predicate);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>transformedPredicate</code> if you want that.
     *
     * @param transformer  the transformer to use
     * @param predicate  the predicate to decorate
     */
    public TransformedPredicate(final Transformer<? super T, ? extends T> transformer,
                                final Predicate<? super T> predicate) {
        iTransformer = transformer;
        iPredicate = predicate;
    }

    /**
     * Evaluates the predicate returning the result of the decorated predicate
     * once the input has been transformed
     *
     * @param object  the input object which will be transformed
     * @return true if decorated predicate returns true
     */
    @Override
    public boolean evaluate(final T object) {
        final T result = iTransformer.transform(object);
        return iPredicate.evaluate(result);
    }

    /**
     * Gets the predicate being decorated.
     *
     * @return the predicate as the only element in an array
     * @since 3.1
     */
    @Override
    @SuppressWarnings("unchecked")
    public Predicate<? super T>[] getPredicates() {
        return new Predicate[] {iPredicate};
    }

    /**
     * Gets the transformer in use.
     *
     * @return the transformer
     */
    public Transformer<? super T, ? extends T> getTransformer() {
        return iTransformer;
    }

}
