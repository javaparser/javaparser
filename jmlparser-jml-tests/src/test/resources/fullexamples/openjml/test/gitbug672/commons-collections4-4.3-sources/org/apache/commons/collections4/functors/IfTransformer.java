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
 * Transformer implementation that will call one of two closures based on whether a predicate evaluates
 * as true or false.
 *
 * @param <I> The input type for the transformer
 * @param <O> The output type for the transformer
 *
 * @since 4.1
 */
public class IfTransformer<I, O> implements Transformer<I, O>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 8069309411242014252L;

    /** The test */
    private final Predicate<? super I> iPredicate;
    /** The transformer to use if true */
    private final Transformer<? super I, ? extends O> iTrueTransformer;
    /** The transformer to use if false */
    private final Transformer<? super I, ? extends O> iFalseTransformer;

    /**
     * Factory method that performs validation.
     *
     * @param <I>  input type for the transformer
     * @param <O>  output type for the transformer
     * @param predicate  predicate to switch on
     * @param trueTransformer  transformer used if true
     * @param falseTransformer  transformer used if false
     * @return the <code>if</code> transformer
     * @throws NullPointerException if either argument is null
     */
    public static <I, O> Transformer<I, O> ifTransformer(final Predicate<? super I> predicate,
                                                         final Transformer<? super I, ? extends O> trueTransformer,
                                                         final Transformer<? super I, ? extends O> falseTransformer) {
        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null");
        }
        if (trueTransformer == null || falseTransformer == null) {
            throw new NullPointerException("Transformers must not be null");
        }

        return new IfTransformer<>(predicate, trueTransformer, falseTransformer);
    }

    /**
     * Factory method that performs validation.
     * <p>
     * This factory creates a transformer that just returns the input object when
     * the predicate is false.
     *
     * @param <T>  input and output type for the transformer
     * @param predicate  predicate to switch on
     * @param trueTransformer  transformer used if true
     * @return the <code>if</code> transformer
     * @throws NullPointerException if either argument is null
     */
    public static <T> Transformer<T, T> ifTransformer(
            final Predicate<? super T> predicate,
            final Transformer<? super T, ? extends T> trueTransformer) {

        if (predicate == null) {
            throw new NullPointerException("Predicate must not be null");
        }
        if (trueTransformer == null) {
            throw new NullPointerException("Transformer must not be null");
        }

        return new IfTransformer<>(predicate, trueTransformer, NOPTransformer.<T>nopTransformer());
    }

    /**
     * Constructor that performs no validation.
     * Use the static factory method <code>ifTransformer</code> if you want that.
     *
     * @param predicate  predicate to switch on, not null
     * @param trueTransformer  transformer used if true, not null
     * @param falseTransformer  transformer used if false, not null
     */
    public IfTransformer(final Predicate<? super I> predicate,
        final Transformer<? super I, ? extends O> trueTransformer,
        final Transformer<? super I, ? extends O> falseTransformer) {

        super();
        iPredicate = predicate;
        iTrueTransformer = trueTransformer;
        iFalseTransformer = falseTransformer;
    }

    /**
     * Transforms the input using the true or false transformer based to the result of the predicate.
     *
     * @param input  the input object to transform
     * @return the transformed result
     */
    @Override
    public O transform(final I input) {
        if(iPredicate.evaluate(input)){
            return iTrueTransformer.transform(input);
        }
        return iFalseTransformer.transform(input);
    }

    /**
     * Gets the predicate.
     *
     * @return the predicate
     */
    public Predicate<? super I> getPredicate(){
        return iPredicate;
    }

    /**
     * Gets the transformer used when true.
     *
     * @return the transformer
     */
    public Transformer<? super I, ? extends O> getTrueTransformer() {
        return iTrueTransformer;
    }

    /**
     * Gets the transformer used when false.
     *
     * @return the transformer
     */
    public Transformer<? super I, ? extends O> getFalseTransformer() {
        return iFalseTransformer;
    }
}
