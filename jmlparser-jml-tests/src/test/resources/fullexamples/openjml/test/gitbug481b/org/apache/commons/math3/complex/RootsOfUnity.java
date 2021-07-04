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
package org.apache.commons.math3.complex;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.FastMath;

/**
 * A helper class for the computation and caching of the {@code n}-th roots of
 * unity.
 *
 * @since 3.0
 */
public class RootsOfUnity implements Serializable {

    /** Serializable version id. */
    private static final long serialVersionUID = 20120201L;

    /** Number of roots of unity. */
    private int omegaCount;

    /** Real part of the roots. */
    private double[] omegaReal;

    /**
     * Imaginary part of the {@code n}-th roots of unity, for positive values
     * of {@code n}. In this array, the roots are stored in counter-clockwise
     * order.
     */
    private double[] omegaImaginaryCounterClockwise;

    /**
     * Imaginary part of the {@code n}-th roots of unity, for negative values
     * of {@code n}. In this array, the roots are stored in clockwise order.
     */
    private double[] omegaImaginaryClockwise;

    /**
     * {@code true} if {@link #computeRoots(int)} was called with a positive
     * value of its argument {@code n}. In this case, counter-clockwise ordering
     * of the roots of unity should be used.
     */
    private boolean isCounterClockWise;

    /**
     * Build an engine for computing the {@code n}-th roots of unity.
     */
    public RootsOfUnity() {

        omegaCount = 0;
        omegaReal = null;
        omegaImaginaryCounterClockwise = null;
        omegaImaginaryClockwise = null;
        isCounterClockWise = true;
    }

    /**
     * Returns {@code true} if {@link #computeRoots(int)} was called with a
     * positive value of its argument {@code n}. If {@code true}, then
     * counter-clockwise ordering of the roots of unity should be used.
     *
     * @return {@code true} if the roots of unity are stored in
     * counter-clockwise order
     * @throws MathIllegalStateException if no roots of unity have been computed
     * yet
     */
    public synchronized boolean isCounterClockWise()
            throws MathIllegalStateException {

        if (omegaCount == 0) {
            throw new MathIllegalStateException(
                    LocalizedFormats.ROOTS_OF_UNITY_NOT_COMPUTED_YET);
        }
        return isCounterClockWise;
    }

    /**
     * <p>
     * Computes the {@code n}-th roots of unity. The roots are stored in
     * {@code omega[]}, such that {@code omega[k] = w ^ k}, where
     * {@code k = 0, ..., n - 1}, {@code w = exp(2 * pi * i / n)} and
     * {@code i = sqrt(-1)}.
     * </p>
     * <p>
     * Note that {@code n} can be positive of negative
     * </p>
     * <ul>
     * <li>{@code abs(n)} is always the number of roots of unity.</li>
     * <li>If {@code n > 0}, then the roots are stored in counter-clockwise order.</li>
     * <li>If {@code n < 0}, then the roots are stored in clockwise order.</p>
     * </ul>
     *
     * @param n the (signed) number of roots of unity to be computed
     * @throws ZeroException if {@code n = 0}
     */
    public synchronized void computeRoots(int n) throws ZeroException {

        if (n == 0) {
            throw new ZeroException(
                    LocalizedFormats.CANNOT_COMPUTE_0TH_ROOT_OF_UNITY);
        }

        isCounterClockWise = n > 0;

        // avoid repetitive calculations
        final int absN = FastMath.abs(n);

        if (absN == omegaCount) {
            return;
        }

        // calculate everything from scratch
        final double t = 2.0 * FastMath.PI / absN;
        final double cosT = FastMath.cos(t);
        final double sinT = FastMath.sin(t);
        omegaReal = new double[absN];
        omegaImaginaryCounterClockwise = new double[absN];
        omegaImaginaryClockwise = new double[absN];
        omegaReal[0] = 1.0;
        omegaImaginaryCounterClockwise[0] = 0.0;
        omegaImaginaryClockwise[0] = 0.0;
        for (int i = 1; i < absN; i++) {
            omegaReal[i] = omegaReal[i - 1] * cosT -
                    omegaImaginaryCounterClockwise[i - 1] * sinT;
            omegaImaginaryCounterClockwise[i] = omegaReal[i - 1] * sinT +
                    omegaImaginaryCounterClockwise[i - 1] * cosT;
            omegaImaginaryClockwise[i] = -omegaImaginaryCounterClockwise[i];
        }
        omegaCount = absN;
    }

    /**
     * Get the real part of the {@code k}-th {@code n}-th root of unity.
     *
     * @param k index of the {@code n}-th root of unity
     * @return real part of the {@code k}-th {@code n}-th root of unity
     * @throws MathIllegalStateException if no roots of unity have been
     * computed yet
     * @throws MathIllegalArgumentException if {@code k} is out of range
     */
    public synchronized double getReal(int k)
            throws MathIllegalStateException, MathIllegalArgumentException {

        if (omegaCount == 0) {
            throw new MathIllegalStateException(
                    LocalizedFormats.ROOTS_OF_UNITY_NOT_COMPUTED_YET);
        }
        if ((k < 0) || (k >= omegaCount)) {
            throw new OutOfRangeException(
                    LocalizedFormats.OUT_OF_RANGE_ROOT_OF_UNITY_INDEX,
                    Integer.valueOf(k),
                    Integer.valueOf(0),
                    Integer.valueOf(omegaCount - 1));
        }

        return omegaReal[k];
    }

    /**
     * Get the imaginary part of the {@code k}-th {@code n}-th root of unity.
     *
     * @param k index of the {@code n}-th root of unity
     * @return imaginary part of the {@code k}-th {@code n}-th root of unity
     * @throws MathIllegalStateException if no roots of unity have been
     * computed yet
     * @throws OutOfRangeException if {@code k} is out of range
     */
    public synchronized double getImaginary(int k)
            throws MathIllegalStateException, OutOfRangeException {

        if (omegaCount == 0) {
            throw new MathIllegalStateException(
                    LocalizedFormats.ROOTS_OF_UNITY_NOT_COMPUTED_YET);
        }
        if ((k < 0) || (k >= omegaCount)) {
            throw new OutOfRangeException(
                    LocalizedFormats.OUT_OF_RANGE_ROOT_OF_UNITY_INDEX,
                    Integer.valueOf(k),
                    Integer.valueOf(0),
                    Integer.valueOf(omegaCount - 1));
        }

        return isCounterClockWise ? omegaImaginaryCounterClockwise[k] :
            omegaImaginaryClockwise[k];
    }

    /**
     * Returns the number of roots of unity currently stored. If
     * {@link #computeRoots(int)} was called with {@code n}, then this method
     * returns {@code abs(n)}. If no roots of unity have been computed yet, this
     * method returns 0.
     *
     * @return the number of roots of unity currently stored
     */
    public synchronized int getNumberOfRoots() {
        return omegaCount;
    }
}
