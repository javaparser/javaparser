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
import org.apache.commons.math3.util.FastMath;

/**
 * Exponential decay function: <code>a e<sup>-x / b</sup></code>,
 * where {@code x} is the (integer) independent variable.
 * <br/>
 * Class is immutable.
 *
 * @since 3.3
 */
public class ExponentialDecayFunction {
    /** Factor {@code a}. */
    private final double a;
    /** Factor {@code 1 / b}. */
    private final double oneOverB;

    /**
     * Creates an instance. It will be such that
     * <ul>
     *  <li>{@code a = initValue}</li>
     *  <li>{@code b = -numCall / ln(valueAtNumCall / initValue)}</li>
     * </ul>
     *
     * @param initValue Initial value, i.e. {@link #value(long) value(0)}.
     * @param valueAtNumCall Value of the function at {@code numCall}.
     * @param numCall Argument for which the function returns
     * {@code valueAtNumCall}.
     * @throws NotStrictlyPositiveException if {@code initValue <= 0}.
     * @throws NotStrictlyPositiveException if {@code valueAtNumCall <= 0}.
     * @throws NumberIsTooLargeException if {@code valueAtNumCall >= initValue}.
     * @throws NotStrictlyPositiveException if {@code numCall <= 0}.
     */
    public ExponentialDecayFunction(double initValue,
                                    double valueAtNumCall,
                                    long numCall) {
        if (initValue <= 0) {
            throw new NotStrictlyPositiveException(initValue);
        }
        if (valueAtNumCall <= 0) {
            throw new NotStrictlyPositiveException(valueAtNumCall);
        }
        if (valueAtNumCall >= initValue) {
            throw new NumberIsTooLargeException(valueAtNumCall, initValue, false);
        }
        if (numCall <= 0) {
            throw new NotStrictlyPositiveException(numCall);
        }

        a = initValue;
        oneOverB = -FastMath.log(valueAtNumCall / initValue) / numCall;
    }

    /**
     * Computes <code>a e<sup>-numCall / b</sup></code>.
     *
     * @param numCall Current step of the training task.
     * @return the value of the function at {@code numCall}.
     */
    public double value(long numCall) {
        return a * FastMath.exp(-numCall * oneOverB);
    }
}
