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
package org.apache.commons.math3.random;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.util.MathUtils;

/**
 * Implementation of a Halton sequence.
 * <p>
 * A Halton sequence is a low-discrepancy sequence generating points in the interval [0, 1] according to
 * <pre>
 *   H(n) = d_0 / b + d_1 / b^2 .... d_j / b^j+1
 *
 *   with
 *
 *   n = d_j * b^j-1 + ... d_1 * b + d_0 * b^0
 * </pre>
 * For higher dimensions, subsequent prime numbers are used as base, e.g. { 2, 3, 5 } for a Halton sequence in R^3.
 * <p>
 * Halton sequences are known to suffer from linear correlation for larger prime numbers, thus the individual digits
 * are usually scrambled. This implementation already comes with support for up to 40 dimensions with optimal weight
 * numbers from <a href="http://etd.lib.fsu.edu/theses/available/etd-07062004-140409/unrestricted/dissertation1.pdf">
 * H. Chi: Scrambled quasirandom sequences and their applications</a>.
 * <p>
 * The generator supports two modes:
 * <ul>
 *   <li>sequential generation of points: {@link #nextVector()}</li>
 *   <li>random access to the i-th point in the sequence: {@link #skipTo(int)}</li>
 * </ul>
 *
 * @see <a href="http://en.wikipedia.org/wiki/Halton_sequence">Halton sequence (Wikipedia)</a>
 * @see <a href="https://lirias.kuleuven.be/bitstream/123456789/131168/1/mcm2005_bartv.pdf">
 * On the Halton sequence and its scramblings</a>
 * @since 3.3
 */
public class HaltonSequenceGenerator implements RandomVectorGenerator {

    /** The first 40 primes. */
    private static final int[] PRIMES = new int[] {
        2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67,
        71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139,
        149, 151, 157, 163, 167, 173
    };

    /** The optimal weights used for scrambling of the first 40 dimension. */
    private static final int[] WEIGHTS = new int[] {
        1, 2, 3, 3, 8, 11, 12, 14, 7, 18, 12, 13, 17, 18, 29, 14, 18, 43, 41,
        44, 40, 30, 47, 65, 71, 28, 40, 60, 79, 89, 56, 50, 52, 61, 108, 56,
        66, 63, 60, 66
    };

    /** Space dimension. */
    private final int dimension;

    /** The current index in the sequence. */
    private int count = 0;

    /** The base numbers for each component. */
    private final int[] base;

    /** The scrambling weights for each component. */
    private final int[] weight;

    /**
     * Construct a new Halton sequence generator for the given space dimension.
     *
     * @param dimension the space dimension
     * @throws OutOfRangeException if the space dimension is outside the allowed range of [1, 40]
     */
    public HaltonSequenceGenerator(final int dimension) throws OutOfRangeException {
        this(dimension, PRIMES, WEIGHTS);
    }

    /**
     * Construct a new Halton sequence generator with the given base numbers and weights for each dimension.
     * The length of the bases array defines the space dimension and is required to be &gt; 0.
     *
     * @param dimension the space dimension
     * @param bases the base number for each dimension, entries should be (pairwise) prime, may not be null
     * @param weights the weights used during scrambling, may be null in which case no scrambling will be performed
     * @throws NullArgumentException if base is null
     * @throws OutOfRangeException if the space dimension is outside the range [1, len], where
     *   len refers to the length of the bases array
     * @throws DimensionMismatchException if weights is non-null and the length of the input arrays differ
     */
    public HaltonSequenceGenerator(final int dimension, final int[] bases, final int[] weights)
            throws NullArgumentException, OutOfRangeException, DimensionMismatchException {

        MathUtils.checkNotNull(bases);

        if (dimension < 1 || dimension > bases.length) {
            throw new OutOfRangeException(dimension, 1, PRIMES.length);
        }

        if (weights != null && weights.length != bases.length) {
            throw new DimensionMismatchException(weights.length, bases.length);
        }

        this.dimension = dimension;
        this.base = bases.clone();
        this.weight = weights == null ? null : weights.clone();
        count = 0;
    }

    /** {@inheritDoc} */
    public double[] nextVector() {
        final double[] v = new double[dimension];
        for (int i = 0; i < dimension; i++) {
            int index = count;
            double f = 1.0 / base[i];

            int j = 0;
            while (index > 0) {
                final int digit = scramble(i, j, base[i], index % base[i]);
                v[i] += f * digit;
                index /= base[i]; // floor( index / base )
                f /= base[i];
            }
        }
        count++;
        return v;
    }

    /**
     * Performs scrambling of digit {@code d_j} according to the formula:
     * <pre>
     *   ( weight_i * d_j ) mod base
     * </pre>
     * Implementations can override this method to do a different scrambling.
     *
     * @param i the dimension index
     * @param j the digit index
     * @param b the base for this dimension
     * @param digit the j-th digit
     * @return the scrambled digit
     */
    protected int scramble(final int i, final int j, final int b, final int digit) {
        return weight != null ? (weight[i] * digit) % b : digit;
    }

    /**
     * Skip to the i-th point in the Halton sequence.
     * <p>
     * This operation can be performed in O(1).
     *
     * @param index the index in the sequence to skip to
     * @return the i-th point in the Halton sequence
     * @throws NotPositiveException if index &lt; 0
     */
    public double[] skipTo(final int index) throws NotPositiveException {
        count = index;
        return nextVector();
    }

    /**
     * Returns the index i of the next point in the Halton sequence that will be returned
     * by calling {@link #nextVector()}.
     *
     * @return the index of the next point
     */
    public int getNextIndex() {
        return count;
    }

}
