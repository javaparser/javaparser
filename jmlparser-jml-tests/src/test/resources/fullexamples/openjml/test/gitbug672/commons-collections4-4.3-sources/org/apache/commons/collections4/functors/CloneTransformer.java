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

import org.apache.commons.collections4.Transformer;

/**
 * Transformer implementation that returns a clone of the input object.
 * <p>
 * Clone is performed using <code>PrototypeFactory.prototypeFactory(input).create()</code>.
 * <p>
 * <b>WARNING:</b> from v4.1 onwards this class will <b>not</b> be serializable anymore
 * in order to prevent potential remote code execution exploits. Please refer to
 * <a href="https://issues.apache.org/jira/browse/COLLECTIONS-580">COLLECTIONS-580</a>
 * for more details.
 *
 * @since 3.0
 */
public class CloneTransformer<T> implements Transformer<T, T> {

    /** Singleton predicate instance */
    @SuppressWarnings("rawtypes") // the singleton instance works for all types
    public static final Transformer INSTANCE = new CloneTransformer<>();

    /**
     * Factory returning the singleton instance.
     *
     * @param <T>  the type of the objects to be cloned
     * @return the singleton instance
     * @since 3.1
     */
    @SuppressWarnings("unchecked") // the singleton instance works for all types
    public static <T> Transformer<T, T> cloneTransformer() {
        return INSTANCE;
    }

    /**
     * Constructor.
     */
    private CloneTransformer() {
        super();
    }

    /**
     * Transforms the input to result by cloning it.
     *
     * @param input  the input object to transform
     * @return the transformed result
     */
    @Override
    public T transform(final T input) {
        if (input == null) {
            return null;
        }
        return PrototypeFactory.prototypeFactory(input).create();
    }

}
