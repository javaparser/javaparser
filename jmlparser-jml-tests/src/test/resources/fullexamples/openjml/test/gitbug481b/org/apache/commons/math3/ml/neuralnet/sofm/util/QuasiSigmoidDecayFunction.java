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

package org.apache.commons.math3.ml.neuralnet.sofm.util;

import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.analysis.function.Logistic;

/**
 * Decay function whose shape is similar to a sigmoid.
 * <br/>
 * Class is immutable.
 *
 * @since 3.3
 */
public class QuasiSigmoidDecayFunction {
    /** Sigmoid. */
    private final Logistic sigmoid;
    /** See {@link #value(long)}. */
    private final double scale;

    /**
     * Creates an instance.
     * The function {@code f} will have the following properties:
     * <ul>
     *  <li>{@code f(0) = initValue}</li>
     *  <li>{@code numCall} is the inflexion point</li>
     *  <li>{@code slope = f'(numCall)}</li>
     * </ul>
     *
     * @param initValue Initial value, i.e. {@link #value(long) value(0)}.
     * @param slope Value of the function derivative at {@code numCall}.
     * @param numCall Inflexion point.
     * @throws NotStrictlyPositiveException if {@code initValue <= 0}.
     * @throws NumberIsTooLargeException if {@code slope >= 0}.
     * @throws NotStrictlyPositiveException if {@code numCall <= 0}.
     */
    public QuasiSigmoidDecayFunction(double initValue,
                                     double slope,
                                     long numCall) {
        if (initValue <= 0) {
            throw new NotStrictlyPositiveException(initValue);
        }
        if (slope >= 0) {
            throw new NumberIsTooLargeException(slope, 0, false);
        }
        if (numCall <= 1) {
            throw new NotStrictlyPositiveException(numCall);
        }

        final double k = initValue;
        final double m = numCall;
        final double b = 4 * slope / initValue;
        final double q = 1;
        final double a = 0;
        final double n = 1;
        sigmoid = new Logistic(k, m, b, q, a, n);

        final double y0 = sigmoid.value(0);
        scale = k / y0;
    }

    /**
     * Computes the value of the learning factor.
     *
     * @param numCall Current step of the training task.
     * @return the value of the function at {@code numCall}.
     */
    public double value(long numCall) {
        return scale * sigmoid.value(numCall);
    }
}
