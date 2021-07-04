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
import org.apache.commons.collections4.Predicate;
import org.apache.commons.collections4.Transformer;

/**
 * Predicate implementation that returns the result of a transformer.
 *
 * @since 3.0
 */
public final class TransformerPredicate<T> implements Predicate<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = -2407966402920578741L;

    /** The transformer to call */
    private final Transformer<? super T, Boolean> iTransformer;

    /**
     * Factory to create the predicate.
     *
     * @param <T> the type that the predicate queries
     * @param transformer  the transformer to decorate
     * @return the predicate
     * @throws NullPointerException if the transformer is null
     */
    public static <T> Predicate<T> transformerPredicate(final Transformer<? super T, Boolean> transformer) {
        if (transformer == null) {
            throw new NullPointerException("The transformer to call must not be null");
        }
        return new TransformerPredicate<>(transformer);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>transformerPredicate</code> if you want that.
     *
     * @param transformer  the transformer to decorate
     */
    public TransformerPredicate(final Transformer<? super T, Boolean> transformer) {
        super();
        iTransformer = transformer;
    }

    /**
     * Evaluates the predicate returning the result of the decorated transformer.
     *
     * @param object  the input object
     * @return true if decorated transformer returns Boolean.TRUE
     * @throws FunctorException if the transformer returns an invalid type
     */
    @Override
    public boolean evaluate(final T object) {
        final Boolean result = iTransformer.transform(object);
        if (result == null) {
            throw new FunctorException(
                    "Transformer must return an instanceof Boolean, it was a null object");
        }
        return result.booleanValue();
    }

    /**
     * Gets the transformer.
     *
     * @return the transformer
     * @since 3.1
     */
    public Transformer<? super T, Boolean> getTransformer() {
        return iTransformer;
    }

}
