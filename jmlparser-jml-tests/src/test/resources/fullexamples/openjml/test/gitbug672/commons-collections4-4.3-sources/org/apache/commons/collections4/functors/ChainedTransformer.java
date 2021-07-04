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
import java.util.Collection;

import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that chains the specified transformers together.
 * <p>
 * The input object is passed to the first transformer. The transformed result
 * is passed to the second transformer and so on.
 *
 * @since 3.0
 */
public class ChainedTransformer<T> implements Transformer<T, T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 3514945074733160196L;

    /** The transformers to call in turn */
    private final Transformer<? super T, ? extends T>[] iTransformers;

    /**
     * Factory method that performs validation and copies the parameter array.
     *
     * @param <T>  the object type
     * @param transformers  the transformers to chain, copied, no nulls
     * @return the <code>chained</code> transformer
     * @throws NullPointerException if the transformers array is null
     * @throws NullPointerException if any transformer in the array is null
     */
    public static <T> Transformer<T, T> chainedTransformer(final Transformer<? super T, ? extends T>... transformers) {
        FunctorUtils.validate(transformers);
        if (transformers.length == 0) {
            return NOPTransformer.<T>nopTransformer();
        }
        return new ChainedTransformer<>(transformers);
    }

    /**
     * Create a new Transformer that calls each transformer in turn, passing the
     * result into the next transformer. The ordering is that of the iterator()
     * method on the collection.
     *
     * @param <T>  the object type
     * @param transformers  a collection of transformers to chain
     * @return the <code>chained</code> transformer
     * @throws NullPointerException if the transformers collection is null
     * @throws NullPointerException if any transformer in the collection is null
     */
    @SuppressWarnings("unchecked")
    public static <T> Transformer<T, T> chainedTransformer(
            final Collection<? extends Transformer<? super T, ? extends T>> transformers) {
        if (transformers == null) {
            throw new NullPointerException("Transformer collection must not be null");
        }
        if (transformers.size() == 0) {
            return NOPTransformer.<T>nopTransformer();
        }
        // convert to array like this to guarantee iterator() ordering
        final Transformer<T, T>[] cmds = transformers.toArray(new Transformer[transformers.size()]);
        FunctorUtils.validate(cmds);
        return new ChainedTransformer<>(false, cmds);
    }

    /**
     * Hidden constructor for the use by the static factory methods.
     *
     * @param clone  if {@code true} the input argument will be cloned
     * @param transformers  the transformers to chain, no nulls
     */
    private ChainedTransformer(final boolean clone, final Transformer<? super T, ? extends T>[] transformers) {
        super();
        iTransformers = clone ? FunctorUtils.copy(transformers) : transformers;
    }

    /**
     * Constructor that performs no validation.
     * Use <code>chainedTransformer</code> if you want that.
     *
     * @param transformers  the transformers to chain, copied, no nulls
     */
    public ChainedTransformer(final Transformer<? super T, ? extends T>... transformers) {
        this(true, transformers);
    }

    /**
     * Transforms the input to result via each decorated transformer
     *
     * @param object  the input object passed to the first transformer
     * @return the transformed result
     */
    @Override
    public T transform(T object) {
        for (final Transformer<? super T, ? extends T> iTransformer : iTransformers) {
            object = iTransformer.transform(object);
        }
        return object;
    }

    /**
     * Gets the transformers.
     *
     * @return a copy of the transformers
     * @since 3.1
     */
    public Transformer<? super T, ? extends T>[] getTransformers() {
        return FunctorUtils.<T, T>copy(iTransformers);
    }

}
