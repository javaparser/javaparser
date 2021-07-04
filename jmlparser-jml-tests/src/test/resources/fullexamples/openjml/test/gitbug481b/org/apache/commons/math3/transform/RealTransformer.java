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
package org.apache.commons.math3.transform;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NonMonotonicSequenceException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;

/**
 * Interface for one-dimensional data sets transformations producing real results.
 * <p>
 * Such transforms include {@link FastSineTransformer sine transform},
 * {@link FastCosineTransformer cosine transform} or {@link
 * FastHadamardTransformer Hadamard transform}. {@link FastFourierTransformer
 * Fourier transform} is of a different kind and does not implement this
 * interface since it produces {@link org.apache.commons.math3.complex.Complex}
 * results instead of real ones.
 *
 * @since 2.0
 */
public interface RealTransformer  {

    /**
     * Returns the (forward, inverse) transform of the specified real data set.
     *
     * @param f the real data array to be transformed (signal)
     * @param type the type of transform (forward, inverse) to be performed
     * @return the real transformed array (spectrum)
     * @throws MathIllegalArgumentException if the array cannot be transformed
     *   with the given type (this may be for example due to array size, which is
     *   constrained in some transforms)
     */
    double[] transform(double[] f, TransformType type) throws MathIllegalArgumentException;

    /**
     * Returns the (forward, inverse) transform of the specified real function,
     * sampled on the specified interval.
     *
     * @param f the function to be sampled and transformed
     * @param min the (inclusive) lower bound for the interval
     * @param max the (exclusive) upper bound for the interval
     * @param n the number of sample points
     * @param type the type of transform (forward, inverse) to be performed
     * @return the real transformed array
     * @throws NonMonotonicSequenceException if the lower bound is greater than, or equal to the upper bound
     * @throws NotStrictlyPositiveException if the number of sample points is negative
     * @throws MathIllegalArgumentException if the sample cannot be transformed
     *   with the given type (this may be for example due to sample size, which is
     *   constrained in some transforms)
     */
    double[] transform(UnivariateFunction f, double min, double max, int n,
                       TransformType type)
        throws NonMonotonicSequenceException, NotStrictlyPositiveException, MathIllegalArgumentException;

}
