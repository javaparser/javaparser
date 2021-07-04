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
import java.util.Comparator;

import org.apache.commons.collections4.Predicate;

/**
 * Predicate that compares the input object with the one stored in the predicate using a comparator.
 * In addition, the comparator result can be evaluated in accordance to a supplied criterion value.
 *
 * <p>In order to demonstrate the use of the predicate, the following variables are declared:</p>
 *
 * <pre>
 * Integer ONE = Integer.valueOf(1);
 * Integer TWO = Integer.valueOf(2);
 *
 * Comparator comparator = new Comparator() {
 *
 *     public int compare(Object first, Object second) {
 *         return ((Integer) second) - ((Integer) first);
 *     }
 *
 * };
 * </pre>
 *
 * <p>Using the declared variables, the <code>ComparatorPredicate</code> can be used used in the
 * following way:</p>
 *
 * <pre>
 * ComparatorPredicate.comparatorPredicate(ONE, comparator).evaluate(TWO);
 * </pre>
 *
 * <p>The input variable <code>TWO</code> in compared to the stored variable <code>ONE</code> using
 * the supplied <code>comparator</code>. This is the default usage of the predicate and will return
 * <code>true</code> if the underlying comparator returns <code>0</code>. In addition to the default
 * usage of the predicate, it is possible to evaluate the comparator's result in several ways. The
 * following {@link Criterion} enumeration values are provided by the predicate:
 * </p>
 *
 * <ul>
 *     <li>EQUAL</li>
 *     <li>GREATER</li>
 *     <li>GREATER_OR_EQUAL</li>
 *     <li>LESS</li>
 *     <li>LESS_OR_EQUAL</li>
 * </ul>
 *
 * <p>The following examples demonstrates how these constants can be used in order to manipulate the
 * evaluation of a comparator result.</p>
 *
 * <pre>
 * ComparatorPredicate.comparatorPredicate(ONE, comparator,<b>ComparatorPredicate.Criterion.GREATER</b>).evaluate(TWO);
 * </pre>
 *
 * <p>The input variable TWO is compared to the stored variable ONE using the supplied <code>comparator</code>
 * using the <code>GREATER</code> evaluation criterion constant. This instructs the predicate to
 * return <code>true</code> if the comparator returns a value greater than <code>0</code>.</p>
 *
 * @since 4.0
 */
public class ComparatorPredicate<T> implements Predicate<T>, Serializable {

    private static final long serialVersionUID = -1863209236504077399L;

    public enum Criterion {
        EQUAL, GREATER, LESS, GREATER_OR_EQUAL, LESS_OR_EQUAL,
    }

    // Instance variables:

    /** The internal object to compare with */
    private final T object;

    /** The comparator to use for comparison */
    private final Comparator<T> comparator;

    /** The comparison evaluation criterion to use */
    private final Criterion criterion;

    /**
     * Factory to create the comparator predicate
     *
     * @param <T> the type that the predicate queries
     * @param object  the object to compare to
     * @param comparator  the comparator to use for comparison
     * @return the predicate
     * @throws NullPointerException if comparator is null
     */
    public static <T> Predicate<T> comparatorPredicate(final T object, final Comparator<T> comparator) {
        return comparatorPredicate(object, comparator, Criterion.EQUAL);
    }

    /**
     * Factory to create the comparator predicate
     *
     * @param <T> the type that the predicate queries
     * @param object  the object to compare to
     * @param comparator  the comparator to use for comparison
     * @param criterion  the criterion to use to evaluate comparison
     * @return the predicate
     * @throws NullPointerException if comparator or criterion is null
     */
    public static <T> Predicate<T> comparatorPredicate(final T object, final Comparator<T> comparator,
                                                       final Criterion criterion) {
        if (comparator == null) {
            throw new NullPointerException("Comparator must not be null.");
        }
        if (criterion == null) {
            throw new NullPointerException("Criterion must not be null.");
        }
        return new ComparatorPredicate<>(object, comparator, criterion);
    }

    /**
     * Constructor that performs no validation.
     * Use <code>comparatorPredicate</code> if you want that.
     *
     * @param object  the object to compare to
     * @param comparator  the comparator to use for comparison
     * @param criterion  the criterion to use to evaluate comparison
     */
    public ComparatorPredicate(final T object, final Comparator<T> comparator, final Criterion criterion) {
        super();
        this.object = object;
        this.comparator = comparator;
        this.criterion = criterion;
    }

    /**
     * Evaluates the predicate. The predicate evaluates to <code>true</code> in the following cases:
     *
     * <ul>
     * <li><code>comparator.compare(object, input) == 0 &amp;&amp; criterion == EQUAL</code></li>
     * <li><code>comparator.compare(object, input) &lt; 0 &amp;&amp; criterion == LESS</code></li>
     * <li><code>comparator.compare(object, input) &gt; 0 &amp;&amp; criterion == GREATER</code></li>
     * <li><code>comparator.compare(object, input) &gt;= 0 &amp;&amp; criterion == GREATER_OR_EQUAL</code></li>
     * <li><code>comparator.compare(object, input) &lt;= 0 &amp;&amp; criterion == LESS_OR_EQUAL</code></li>
     * </ul>
     *
     * @see org.apache.commons.collections4.Predicate#evaluate(java.lang.Object)
     * @see java.util.Comparator#compare(java.lang.Object first, java.lang.Object second)
     *
     * @param target  the target object to compare to
     * @return {@code true} if the comparison succeeds according to the selected criterion
     * @throws IllegalStateException if the criterion is invalid (really not possible)
     */
    @Override
    public boolean evaluate(final T target) {

        boolean result = false;
        final int comparison = comparator.compare(object, target);
        switch (criterion) {
        case EQUAL:
            result = comparison == 0;
            break;
        case GREATER:
            result = comparison > 0;
            break;
        case LESS:
            result = comparison < 0;
            break;
        case GREATER_OR_EQUAL:
            result = comparison >= 0;
            break;
        case LESS_OR_EQUAL:
            result = comparison <= 0;
            break;
        default:
            throw new IllegalStateException("The current criterion '" + criterion + "' is invalid.");
        }

        return result;
    }
}
