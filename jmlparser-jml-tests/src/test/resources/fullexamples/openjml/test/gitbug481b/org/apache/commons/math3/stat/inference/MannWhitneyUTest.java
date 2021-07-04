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
package org.apache.commons.math3.stat.inference;

import org.apache.commons.math3.distribution.NormalDistribution;
import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.stat.ranking.NaNStrategy;
import org.apache.commons.math3.stat.ranking.NaturalRanking;
import org.apache.commons.math3.stat.ranking.TiesStrategy;
import org.apache.commons.math3.util.FastMath;

/**
 * An implementation of the Mann-Whitney U test (also called Wilcoxon rank-sum test).
 *
 */
public class MannWhitneyUTest {

    /** Ranking algorithm. */
    private NaturalRanking naturalRanking;

    /**
     * Create a test instance using where NaN's are left in place and ties get
     * the average of applicable ranks. Use this unless you are very sure of
     * what you are doing.
     */
    public MannWhitneyUTest() {
        naturalRanking = new NaturalRanking(NaNStrategy.FIXED,
                TiesStrategy.AVERAGE);
    }

    /**
     * Create a test instance using the given strategies for NaN's and ties.
     * Only use this if you are sure of what you are doing.
     *
     * @param nanStrategy
     *            specifies the strategy that should be used for Double.NaN's
     * @param tiesStrategy
     *            specifies the strategy that should be used for ties
     */
    public MannWhitneyUTest(final NaNStrategy nanStrategy,
                            final TiesStrategy tiesStrategy) {
        naturalRanking = new NaturalRanking(nanStrategy, tiesStrategy);
    }

    /**
     * Ensures that the provided arrays fulfills the assumptions.
     *
     * @param x first sample
     * @param y second sample
     * @throws NullArgumentException if {@code x} or {@code y} are {@code null}.
     * @throws NoDataException if {@code x} or {@code y} are zero-length.
     */
    private void ensureDataConformance(final double[] x, final double[] y)
        throws NullArgumentException, NoDataException {

        if (x == null ||
            y == null) {
            throw new NullArgumentException();
        }
        if (x.length == 0 ||
            y.length == 0) {
            throw new NoDataException();
        }
    }

    /** Concatenate the samples into one array.
     * @param x first sample
     * @param y second sample
     * @return concatenated array
     */
    private double[] concatenateSamples(final double[] x, final double[] y) {
        final double[] z = new double[x.length + y.length];

        System.arraycopy(x, 0, z, 0, x.length);
        System.arraycopy(y, 0, z, x.length, y.length);

        return z;
    }

    /**
     * Computes the <a
     * href="http://en.wikipedia.org/wiki/Mann%E2%80%93Whitney_U"> Mann-Whitney
     * U statistic</a> comparing mean for two independent samples possibly of
     * different length.
     * <p>
     * This statistic can be used to perform a Mann-Whitney U test evaluating
     * the null hypothesis that the two independent samples has equal mean.
     * </p>
     * <p>
     * Let X<sub>i</sub> denote the i'th individual of the first sample and
     * Y<sub>j</sub> the j'th individual in the second sample. Note that the
     * samples would often have different length.
     * </p>
     * <p>
     * <strong>Preconditions</strong>:
     * <ul>
     * <li>All observations in the two samples are independent.</li>
     * <li>The observations are at least ordinal (continuous are also ordinal).</li>
     * </ul>
     * </p>
     *
     * @param x the first sample
     * @param y the second sample
     * @return Mann-Whitney U statistic (maximum of U<sup>x</sup> and U<sup>y</sup>)
     * @throws NullArgumentException if {@code x} or {@code y} are {@code null}.
     * @throws NoDataException if {@code x} or {@code y} are zero-length.
     */
    public double mannWhitneyU(final double[] x, final double[] y)
        throws NullArgumentException, NoDataException {

        ensureDataConformance(x, y);

        final double[] z = concatenateSamples(x, y);
        final double[] ranks = naturalRanking.rank(z);

        double sumRankX = 0;

        /*
         * The ranks for x is in the first x.length entries in ranks because x
         * is in the first x.length entries in z
         */
        for (int i = 0; i < x.length; ++i) {
            sumRankX += ranks[i];
        }

        /*
         * U1 = R1 - (n1 * (n1 + 1)) / 2 where R1 is sum of ranks for sample 1,
         * e.g. x, n1 is the number of observations in sample 1.
         */
        final double U1 = sumRankX - ((long) x.length * (x.length + 1)) / 2;

        /*
         * It can be shown that U1 + U2 = n1 * n2
         */
        final double U2 = (long) x.length * y.length - U1;

        return FastMath.max(U1, U2);
    }

    /**
     * @param Umin smallest Mann-Whitney U value
     * @param n1 number of subjects in first sample
     * @param n2 number of subjects in second sample
     * @return two-sided asymptotic p-value
     * @throws ConvergenceException if the p-value can not be computed
     * due to a convergence error
     * @throws MaxCountExceededException if the maximum number of
     * iterations is exceeded
     */
    private double calculateAsymptoticPValue(final double Umin,
                                             final int n1,
                                             final int n2)
        throws ConvergenceException, MaxCountExceededException {

        /* long multiplication to avoid overflow (double not used due to efficiency
         * and to avoid precision loss)
         */
        final long n1n2prod = (long) n1 * n2;

        // http://en.wikipedia.org/wiki/Mann%E2%80%93Whitney_U#Normal_approximation
        final double EU = n1n2prod / 2.0;
        final double VarU = n1n2prod * (n1 + n2 + 1) / 12.0;

        final double z = (Umin - EU) / FastMath.sqrt(VarU);

        // No try-catch or advertised exception because args are valid
        // pass a null rng to avoid unneeded overhead as we will not sample from this distribution
        final NormalDistribution standardNormal = new NormalDistribution(null, 0, 1);

        return 2 * standardNormal.cumulativeProbability(z);
    }

    /**
     * Returns the asymptotic <i>observed significance level</i>, or <a href=
     * "http://www.cas.lancs.ac.uk/glossary_v1.1/hyptest.html#pvalue">
     * p-value</a>, associated with a <a
     * href="http://en.wikipedia.org/wiki/Mann%E2%80%93Whitney_U"> Mann-Whitney
     * U statistic</a> comparing mean for two independent samples.
     * <p>
     * Let X<sub>i</sub> denote the i'th individual of the first sample and
     * Y<sub>j</sub> the j'th individual in the second sample. Note that the
     * samples would often have different length.
     * </p>
     * <p>
     * <strong>Preconditions</strong>:
     * <ul>
     * <li>All observations in the two samples are independent.</li>
     * <li>The observations are at least ordinal (continuous are also ordinal).</li>
     * </ul>
     * </p><p>
     * Ties give rise to biased variance at the moment. See e.g. <a
     * href="http://mlsc.lboro.ac.uk/resources/statistics/Mannwhitney.pdf"
     * >http://mlsc.lboro.ac.uk/resources/statistics/Mannwhitney.pdf</a>.</p>
     *
     * @param x the first sample
     * @param y the second sample
     * @return asymptotic p-value
     * @throws NullArgumentException if {@code x} or {@code y} are {@code null}.
     * @throws NoDataException if {@code x} or {@code y} are zero-length.
     * @throws ConvergenceException if the p-value can not be computed due to a
     * convergence error
     * @throws MaxCountExceededException if the maximum number of iterations
     * is exceeded
     */
    public double mannWhitneyUTest(final double[] x, final double[] y)
        throws NullArgumentException, NoDataException,
        ConvergenceException, MaxCountExceededException {

        ensureDataConformance(x, y);

        final double Umax = mannWhitneyU(x, y);

        /*
         * It can be shown that U1 + U2 = n1 * n2
         */
        final double Umin = (long) x.length * y.length - Umax;

        return calculateAsymptoticPValue(Umin, x.length, y.length);
    }

}
