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

package org.apache.commons.math3.ml.neuralnet.sofm;

import org.apache.commons.math3.ml.neuralnet.sofm.util.ExponentialDecayFunction;
import org.apache.commons.math3.ml.neuralnet.sofm.util.QuasiSigmoidDecayFunction;
import org.apache.commons.math3.util.FastMath;

/**
 * Factory for creating instances of {@link NeighbourhoodSizeFunction}.
 *
 * @since 3.3
 */
public class NeighbourhoodSizeFunctionFactory {
    /** Class contains only static methods. */
    private NeighbourhoodSizeFunctionFactory() {}

    /**
     * Creates an exponential decay {@link NeighbourhoodSizeFunction function}.
     * It will compute <code>a e<sup>-x / b</sup></code>,
     * where {@code x} is the (integer) independent variable and
     * <ul>
     *  <li><code>a = initValue</code>
     *  <li><code>b = -numCall / ln(valueAtNumCall / initValue)</code>
     * </ul>
     *
     * @param initValue Initial value, i.e.
     * {@link NeighbourhoodSizeFunction#value(long) value(0)}.
     * @param valueAtNumCall Value of the function at {@code numCall}.
     * @param numCall Argument for which the function returns
     * {@code valueAtNumCall}.
     * @return the neighbourhood size function.
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code initValue <= 0}.
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code valueAtNumCall <= 0}.
     * @throws org.apache.commons.math3.exception.NumberIsTooLargeException
     * if {@code valueAtNumCall >= initValue}.
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code numCall <= 0}.
     */
    public static NeighbourhoodSizeFunction exponentialDecay(final double initValue,
                                                             final double valueAtNumCall,
                                                             final long numCall) {
        return new NeighbourhoodSizeFunction() {
            /** DecayFunction. */
            private final ExponentialDecayFunction decay
                = new ExponentialDecayFunction(initValue, valueAtNumCall, numCall);

            /** {@inheritDoc} */
            public int value(long n) {
                return (int) FastMath.rint(decay.value(n));
            }
        };
    }

    /**
     * Creates an sigmoid-like {@code NeighbourhoodSizeFunction function}.
     * The function {@code f} will have the following properties:
     * <ul>
     *  <li>{@code f(0) = initValue}</li>
     *  <li>{@code numCall} is the inflexion point</li>
     *  <li>{@code slope = f'(numCall)}</li>
     * </ul>
     *
     * @param initValue Initial value, i.e.
     * {@link NeighbourhoodSizeFunction#value(long) value(0)}.
     * @param slope Value of the function derivative at {@code numCall}.
     * @param numCall Inflexion point.
     * @return the neighbourhood size function.
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code initValue <= 0}.
     * @throws org.apache.commons.math3.exception.NumberIsTooLargeException
     * if {@code slope >= 0}.
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code numCall <= 0}.
     */
    public static NeighbourhoodSizeFunction quasiSigmoidDecay(final double initValue,
                                                              final double slope,
                                                              final long numCall) {
        return new NeighbourhoodSizeFunction() {
            /** DecayFunction. */
            private final QuasiSigmoidDecayFunction decay
                = new QuasiSigmoidDecayFunction(initValue, slope, numCall);

            /** {@inheritDoc} */
            public int value(long n) {
                return (int) FastMath.rint(decay.value(n));
            }
        };
    }
}
