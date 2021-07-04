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
package org.apache.commons.math3.analysis.integration.gauss;

import java.math.BigDecimal;
import java.math.MathContext;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.util.Pair;

/**
 * Factory that creates Gauss-type quadrature rule using Legendre polynomials.
 * In this implementation, the lower and upper bounds of the natural interval
 * of integration are -1 and 1, respectively.
 * The Legendre polynomials are evaluated using the recurrence relation
 * presented in <a href="http://en.wikipedia.org/wiki/Abramowitz_and_Stegun">
 * Abramowitz and Stegun, 1964</a>.
 *
 * @since 3.1
 */
public class LegendreHighPrecisionRuleFactory extends BaseRuleFactory<BigDecimal> {
    /** Settings for enhanced precision computations. */
    private final MathContext mContext;
    /** The number {@code 2}. */
    private final BigDecimal two;
    /** The number {@code -1}. */
    private final BigDecimal minusOne;
    /** The number {@code 0.5}. */
    private final BigDecimal oneHalf;

    /**
     * Default precision is {@link MathContext#DECIMAL128 DECIMAL128}.
     */
    public LegendreHighPrecisionRuleFactory() {
        this(MathContext.DECIMAL128);
    }

    /**
     * @param mContext Precision setting for computing the quadrature rules.
     */
    public LegendreHighPrecisionRuleFactory(MathContext mContext) {
        this.mContext = mContext;
        two = new BigDecimal("2", mContext);
        minusOne = new BigDecimal("-1", mContext);
        oneHalf = new BigDecimal("0.5", mContext);
    }

    /** {@inheritDoc} */
    @Override
    protected Pair<BigDecimal[], BigDecimal[]> computeRule(int numberOfPoints)
        throws DimensionMismatchException {

        if (numberOfPoints == 1) {
            // Break recursion.
            return new Pair<BigDecimal[], BigDecimal[]>(new BigDecimal[] { BigDecimal.ZERO },
                                                        new BigDecimal[] { two });
        }

        // Get previous rule.
        // If it has not been computed yet it will trigger a recursive call
        // to this method.
        final BigDecimal[] previousPoints = getRuleInternal(numberOfPoints - 1).getFirst();

        // Compute next rule.
        final BigDecimal[] points = new BigDecimal[numberOfPoints];
        final BigDecimal[] weights = new BigDecimal[numberOfPoints];

        // Find i-th root of P[n+1] by bracketing.
        final int iMax = numberOfPoints / 2;
        for (int i = 0; i < iMax; i++) {
            // Lower-bound of the interval.
            BigDecimal a = (i == 0) ? minusOne : previousPoints[i - 1];
            // Upper-bound of the interval.
            BigDecimal b = (iMax == 1) ? BigDecimal.ONE : previousPoints[i];
            // P[j-1](a)
            BigDecimal pma = BigDecimal.ONE;
            // P[j](a)
            BigDecimal pa = a;
            // P[j-1](b)
            BigDecimal pmb = BigDecimal.ONE;
            // P[j](b)
            BigDecimal pb = b;
            for (int j = 1; j < numberOfPoints; j++) {
                final BigDecimal b_two_j_p_1 = new BigDecimal(2 * j + 1, mContext);
                final BigDecimal b_j = new BigDecimal(j, mContext);
                final BigDecimal b_j_p_1 = new BigDecimal(j + 1, mContext);

                // Compute P[j+1](a)
                // ppa = ((2 * j + 1) * a * pa - j * pma) / (j + 1);

                BigDecimal tmp1 = a.multiply(b_two_j_p_1, mContext);
                tmp1 = pa.multiply(tmp1, mContext);
                BigDecimal tmp2 = pma.multiply(b_j, mContext);
                // P[j+1](a)
                BigDecimal ppa = tmp1.subtract(tmp2, mContext);
                ppa = ppa.divide(b_j_p_1, mContext);

                // Compute P[j+1](b)
                // ppb = ((2 * j + 1) * b * pb - j * pmb) / (j + 1);

                tmp1 = b.multiply(b_two_j_p_1, mContext);
                tmp1 = pb.multiply(tmp1, mContext);
                tmp2 = pmb.multiply(b_j, mContext);
                // P[j+1](b)
                BigDecimal ppb = tmp1.subtract(tmp2, mContext);
                ppb = ppb.divide(b_j_p_1, mContext);

                pma = pa;
                pa = ppa;
                pmb = pb;
                pb = ppb;
            }
            // Now pa = P[n+1](a), and pma = P[n](a). Same holds for b.
            // Middle of the interval.
            BigDecimal c = a.add(b, mContext).multiply(oneHalf, mContext);
            // P[j-1](c)
            BigDecimal pmc = BigDecimal.ONE;
            // P[j](c)
            BigDecimal pc = c;
            boolean done = false;
            while (!done) {
                BigDecimal tmp1 = b.subtract(a, mContext);
                BigDecimal tmp2 = c.ulp().multiply(BigDecimal.TEN, mContext);
                done = tmp1.compareTo(tmp2) <= 0;
                pmc = BigDecimal.ONE;
                pc = c;
                for (int j = 1; j < numberOfPoints; j++) {
                    final BigDecimal b_two_j_p_1 = new BigDecimal(2 * j + 1, mContext);
                    final BigDecimal b_j = new BigDecimal(j, mContext);
                    final BigDecimal b_j_p_1 = new BigDecimal(j + 1, mContext);

                    // Compute P[j+1](c)
                    tmp1 = c.multiply(b_two_j_p_1, mContext);
                    tmp1 = pc.multiply(tmp1, mContext);
                    tmp2 = pmc.multiply(b_j, mContext);
                    // P[j+1](c)
                    BigDecimal ppc = tmp1.subtract(tmp2, mContext);
                    ppc = ppc.divide(b_j_p_1, mContext);

                    pmc = pc;
                    pc = ppc;
                }
                // Now pc = P[n+1](c) and pmc = P[n](c).
                if (!done) {
                    if (pa.signum() * pc.signum() <= 0) {
                        b = c;
                        pmb = pmc;
                        pb = pc;
                    } else {
                        a = c;
                        pma = pmc;
                        pa = pc;
                    }
                    c = a.add(b, mContext).multiply(oneHalf, mContext);
                }
            }
            final BigDecimal nP = new BigDecimal(numberOfPoints, mContext);
            BigDecimal tmp1 = pmc.subtract(c.multiply(pc, mContext), mContext);
            tmp1 = tmp1.multiply(nP);
            tmp1 = tmp1.pow(2, mContext);
            BigDecimal tmp2 = c.pow(2, mContext);
            tmp2 = BigDecimal.ONE.subtract(tmp2, mContext);
            tmp2 = tmp2.multiply(two, mContext);
            tmp2 = tmp2.divide(tmp1, mContext);

            points[i] = c;
            weights[i] = tmp2;

            final int idx = numberOfPoints - i - 1;
            points[idx] = c.negate(mContext);
            weights[idx] = tmp2;
        }
        // If "numberOfPoints" is odd, 0 is a root.
        // Note: as written, the test for oddness will work for negative
        // integers too (although it is not necessary here), preventing
        // a FindBugs warning.
        if (numberOfPoints % 2 != 0) {
            BigDecimal pmc = BigDecimal.ONE;
            for (int j = 1; j < numberOfPoints; j += 2) {
                final BigDecimal b_j = new BigDecimal(j, mContext);
                final BigDecimal b_j_p_1 = new BigDecimal(j + 1, mContext);

                // pmc = -j * pmc / (j + 1);
                pmc = pmc.multiply(b_j, mContext);
                pmc = pmc.divide(b_j_p_1, mContext);
                pmc = pmc.negate(mContext);
            }

            // 2 / pow(numberOfPoints * pmc, 2);
            final BigDecimal nP = new BigDecimal(numberOfPoints, mContext);
            BigDecimal tmp1 = pmc.multiply(nP, mContext);
            tmp1 = tmp1.pow(2, mContext);
            BigDecimal tmp2 = two.divide(tmp1, mContext);

            points[iMax] = BigDecimal.ZERO;
            weights[iMax] = tmp2;
        }

        return new Pair<BigDecimal[], BigDecimal[]>(points, weights);
    }
}
