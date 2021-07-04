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

/**
 * Predicate implementation that always returns true.
 *
 * @since 3.0
 */
public final class TruePredicate<T> implements Predicate<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = 3374767158756189740L;

    /** Singleton predicate instance */
    @SuppressWarnings("rawtypes")
    public static final Predicate INSTANCE = new TruePredicate<>();

    /**
     * Factory returning the singleton instance.
     *
     * @param <T> the type that the predicate queries
     * @return the singleton instance
     * @since 3.1
     */
    @SuppressWarnings("unchecked")
    public static <T> Predicate<T> truePredicate() {
        return INSTANCE;
    }

    /**
     * Restricted constructor.
     */
    private TruePredicate() {
        super();
    }

    /**
     * Evaluates the predicate returning true always.
     *
     * @param object  the input object
     * @return true always
     */
    @Override
    public boolean evaluate(final T object) {
        return true;
    }

    private Object readResolve() {
        return INSTANCE;
    }

}
