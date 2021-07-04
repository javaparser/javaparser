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
 * Abstract base class for quantification predicates, e.g. All, Any, None.
 *
 * @since 4.0
 */
public abstract class AbstractQuantifierPredicate<T> implements PredicateDecorator<T>, Serializable {

    /** Serial version UID */
    private static final long serialVersionUID = -3094696765038308799L;

    /** The array of predicates to call */
    protected final Predicate<? super T>[] iPredicates;

    /**
     * Constructor that performs no validation.
     *
     * @param predicates  the predicates to check, not cloned, not null
     */
    public AbstractQuantifierPredicate(final Predicate<? super T>... predicates) {
        iPredicates = predicates;
    }

    /**
     * Gets the predicates.
     *
     * @return a copy of the predicates
     * @since 3.1
     */
    @Override
    public Predicate<? super T>[] getPredicates() {
        return FunctorUtils.<T>copy(iPredicates);
    }

}
