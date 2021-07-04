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
 * Predicate implementation that returns true if either of the predicates return true.
 *
 * @since 3.0
 */
public final class OrPredicate<T> implements PredicateDecorator<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = -8791518325735182855L;

    /** The array of predicates to call */
    private final Predicate<? super T> iPredicate1;
    /** The array of predicates to call */
    private final Predicate<? super T> iPredicate2;

    /**
     * Factory to create the predicate.
     *
     * @param <T> the type that the predicate queries
     * @param predicate1  the first predicate to check, not null
     * @param predicate2  the second predicate to check, not null
     * @return the <code>and</code> predicate
     * @throws NullPointerException if either predicate is null
     */
    public static <T> Predicate<T> orPredicate(final Predicate<? super T> predicate1,
                                               final Predicate<? super T> predicate2) {
        if (predicate1 == null || predicate2 == null) {
            throw new NullPointerException("Predicate must not be null");
        }
        return new OrPredicate<>(predicate1, predicate2);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>orPredicate</code> if you want that.
     *
     * @param predicate1  the first predicate to check, not null
     * @param predicate2  the second predicate to check, not null
     */
    public OrPredicate(final Predicate<? super T> predicate1, final Predicate<? super T> predicate2) {
        super();
        iPredicate1 = predicate1;
        iPredicate2 = predicate2;
    }

    /**
     * Evaluates the predicate returning true if either predicate returns true.
     *
     * @param object  the input object
     * @return true if either decorated predicate returns true
     */
    @Override
    public boolean evaluate(final T object) {
       return iPredicate1.evaluate(object) || iPredicate2.evaluate(object);
    }

    /**
     * Gets the two predicates being decorated as an array.
     *
     * @return the predicates
     * @since 3.1
     */
    @Override
    @SuppressWarnings("unchecked")
    public Predicate<? super T>[] getPredicates() {
        return new Predicate[] {iPredicate1, iPredicate2};
    }

}
