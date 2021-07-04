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

/**
 * Closure implementation that does nothing.
 *
 * @since 3.0
 */
public final class NOPClosure<E> implements Closure<E>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 3518477308466486130L;

    /** Singleton predicate instance */
    @SuppressWarnings("rawtypes")
    public static final Closure INSTANCE = new NOPClosure<>();

    /**
     * Factory returning the singleton instance.
     *
     * @param <E> the type that the closure acts on
     * @return the singleton instance
     * @since 3.1
     */
    @SuppressWarnings("unchecked")
    public static <E> Closure<E> nopClosure() {
        return INSTANCE;
    }

    /**
     * Constructor.
     */
    private NOPClosure() {
        super();
    }

    /**
     * Do nothing.
     *
     * @param input  the input object
     */
    @Override
    public void execute(final E input) {
        // do nothing
    }

    private Object readResolve() {
        return INSTANCE;
    }

}
