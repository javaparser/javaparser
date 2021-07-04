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
package org.apache.commons.math3.util;

import java.util.Iterator;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.MathUnsupportedOperationException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.ZeroException;

/**
 * Provides a sequence of integers.
 *
 * @since 3.6
 */
public class IntegerSequence {
    /**
     * Utility class contains only static methods.
     */
    private IntegerSequence() {}

    /**
     * Creates a sequence {@code [start .. end]}.
     * It calls {@link #range(int,int,int) range(start, end, 1)}.
     *
     * @param start First value of the range.
     * @param end Last value of the range.
     * @return a range.
     */
    public static Range range(int start,
                              int end) {
        return range(start, end, 1);
    }

    /**
     * Creates a sequence \( a_i, i < 0 <= n \)
     * where \( a_i = start + i * step \)
     * and \( n \) is such that \( a_n <= max \) and \( a_{n+1} > max \).
     *
     * @param start First value of the range.
     * @param max Last value of the range that satisfies the above
     * construction rule.
     * @param step Increment.
     * @return a range.
     */
    public static Range range(final int start,
                              final int max,
                              final int step) {
        return new Range(start, max, step);
    }

    /**
     * Generates a sequence of integers.
     */
    public static class Range implements Iterable<Integer> {
        /** Number of integers contained in this range. */
        private final int size;
        /** First value. */
        private final int start;
        /** Final value. */
        private final int max;
        /** Increment. */
        private final int step;

        /**
         * Creates a sequence \( a_i, i < 0 <= n \)
         * where \( a_i = start + i * step \)
         * and \( n \) is such that \( a_n <= max \) and \( a_{n+1} > max \).
         *
         * @param start First value of the range.
         * @param max Last value of the range that satisfies the above
         * construction rule.
         * @param step Increment.
         */
        public Range(int start,
                     int max,
                     int step) {
            this.start = start;
            this.max = max;
            this.step = step;

            final int s = (max - start) / step + 1;
            this.size = s < 0 ? 0 : s;
        }

        /**
         * Gets the number of elements contained in the range.
         *
         * @return the size of the range.
         */
        public int size() {
            return size;
        }

        /** {@inheritDoc} */
        public Iterator<Integer> iterator() {
            return Incrementor.create()
                .withStart(start)
                .withMaximalCount(max + (step > 0 ? 1 : -1))
                .withIncrement(step);
        }
    }

    /**
     * Utility that increments a counter until a maximum is reached, at
     * which point, the instance will by default throw a
     * {@link MaxCountExceededException}.
     * However, the user is able to override this behaviour by defining a
     * custom {@link MaxCountExceededCallback callback}, in order to e.g.
     * select which exception must be thrown.
     */
    public static class Incrementor implements Iterator<Integer> {
        /** Default callback. */
        private static final MaxCountExceededCallback CALLBACK
            = new MaxCountExceededCallback() {
                    /** {@inheritDoc} */
                    public void trigger(int max) throws MaxCountExceededException {
                        throw new MaxCountExceededException(max);
                    }
                };

        /** Initial value the counter. */
        private final int init;
        /** Upper limit for the counter. */
        private final int maximalCount;
        /** Increment. */
        private final int increment;
        /** Function called at counter exhaustion. */
        private final MaxCountExceededCallback maxCountCallback;
        /** Current count. */
        private int count = 0;

        /**
         * Defines a method to be called at counter exhaustion.
         * The {@link #trigger(int) trigger} method should usually throw an exception.
         */
        public interface MaxCountExceededCallback {
            /**
             * Function called when the maximal count has been reached.
             *
             * @param maximalCount Maximal count.
             * @throws MaxCountExceededException at counter exhaustion
             */
            void trigger(int maximalCount) throws MaxCountExceededException;
        }

        /**
         * Creates an incrementor.
         * The counter will be exhausted either when {@code max} is reached
         * or when {@code nTimes} increments have been performed.
         *
         * @param start Initial value.
         * @param max Maximal count.
         * @param step Increment.
         * @param cb Function to be called when the maximal count has been reached.
         * @throws NullArgumentException if {@code cb} is {@code null}.
         */
        private Incrementor(int start,
                            int max,
                            int step,
                            MaxCountExceededCallback cb)
            throws NullArgumentException {
            if (cb == null) {
                throw new NullArgumentException();
            }
            this.init = start;
            this.maximalCount = max;
            this.increment = step;
            this.maxCountCallback = cb;
            this.count = start;
        }

        /**
         * Factory method that creates a default instance.
         * The initial and maximal values are set to 0.
         * For the new instance to be useful, the maximal count must be set
         * by calling {@link #withMaximalCount(int) withMaximalCount}.
         *
         * @return an new instance.
         */
        public static Incrementor create() {
            return new Incrementor(0, 0, 1, CALLBACK);
        }

        /**
         * Creates a new instance with a given initial value.
         * The counter is reset to the initial value.
         *
         * @param start Initial value of the counter.
         * @return a new instance.
         */
        public Incrementor withStart(int start) {
            return new Incrementor(start,
                                   this.maximalCount,
                                   this.increment,
                                   this.maxCountCallback);
        }

        /**
         * Creates a new instance with a given maximal count.
         * The counter is reset to the initial value.
         *
         * @param max Maximal count.
         * @return a new instance.
         */
        public Incrementor withMaximalCount(int max) {
            return new Incrementor(this.init,
                                   max,
                                   this.increment,
                                   this.maxCountCallback);
        }

        /**
         * Creates a new instance with a given increment.
         * The counter is reset to the initial value.
         *
         * @param step Increment.
         * @return a new instance.
         */
        public Incrementor withIncrement(int step) {
            if (step == 0) {
                throw new ZeroException();
            }
            return new Incrementor(this.init,
                                   this.maximalCount,
                                   step,
                                   this.maxCountCallback);
        }

        /**
         * Creates a new instance with a given callback.
         * The counter is reset to the initial value.
         *
         * @param cb Callback to be called at counter exhaustion.
         * @return a new instance.
         */
        public Incrementor withCallback(MaxCountExceededCallback cb) {
            return new Incrementor(this.init,
                                   this.maximalCount,
                                   this.increment,
                                   cb);
        }

        /**
         * Gets the upper limit of the counter.
         *
         * @return the counter upper limit.
         */
        public int getMaximalCount() {
            return maximalCount;
        }

        /**
         * Gets the current count.
         *
         * @return the current count.
         */
        public int getCount() {
            return count;
        }

        /**
         * Checks whether incrementing the counter {@code nTimes} is allowed.
         *
         * @return {@code false} if calling {@link #increment()}
         * will trigger a {@code MaxCountExceededException},
         * {@code true} otherwise.
         */
        public boolean canIncrement() {
            return canIncrement(1);
        }

        /**
         * Checks whether incrementing the counter several times is allowed.
         *
         * @param nTimes Number of increments.
         * @return {@code false} if calling {@link #increment(int)
         * increment(nTimes)} would call the {@link MaxCountExceededCallback callback}
         * {@code true} otherwise.
         */
        public boolean canIncrement(int nTimes) {
            final int finalCount = count + nTimes * increment;
            return increment < 0 ?
                finalCount > maximalCount :
                finalCount < maximalCount;
        }

        /**
         * Performs multiple increments.
         *
         * @param nTimes Number of increments.
         * @throws MaxCountExceededException at counter exhaustion.
         * @throws NotStrictlyPositiveException if {@code nTimes <= 0}.
         *
         * @see #increment()
         */
        public void increment(int nTimes) throws MaxCountExceededException {
            if (nTimes <= 0) {
                throw new NotStrictlyPositiveException(nTimes);
            }

            if (!canIncrement(0)) {
                maxCountCallback.trigger(maximalCount);
            }
            count += nTimes * increment;
        }

        /**
         * Adds the increment value to the current iteration count.
         * At counter exhaustion, this method will call the
         * {@link MaxCountExceededCallback#trigger(int) trigger} method of the
         * callback object passed to the
         * {@link #withCallback(MaxCountExceededCallback)} method.
         * If not explicitly set, a default callback is used that will throw
         * a {@code MaxCountExceededException}.
         *
         * @throws MaxCountExceededException at counter exhaustion, unless a
         * custom {@link MaxCountExceededCallback callback} has been set.
         *
         * @see #increment(int)
         */
        public void increment() throws MaxCountExceededException {
            increment(1);
        }

        /** {@inheritDoc} */
        public boolean hasNext() {
            return canIncrement(0);
        }

        /** {@inheritDoc} */
        public Integer next() {
            final int value = count;
            increment();
            return value;
        }

        /**
         * Not applicable.
         *
         * @throws MathUnsupportedOperationException
         */
        public void remove() {
            throw new MathUnsupportedOperationException();
        }
    }
}
