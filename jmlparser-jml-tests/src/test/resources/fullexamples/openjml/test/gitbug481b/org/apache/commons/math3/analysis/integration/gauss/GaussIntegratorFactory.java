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

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.util.Pair;

/**
 * Class that provides different ways to compute the nodes and weights to be
 * used by the {@link GaussIntegrator Gaussian integration rule}.
 *
 * @since 3.1
 */
public class GaussIntegratorFactory {
    /** Generator of Gauss-Legendre integrators. */
    private final BaseRuleFactory<Double> legendre = new LegendreRuleFactory();
    /** Generator of Gauss-Legendre integrators. */
    private final BaseRuleFactory<BigDecimal> legendreHighPrecision = new LegendreHighPrecisionRuleFactory();
    /** Generator of Gauss-Hermite integrators. */
    private final BaseRuleFactory<Double> hermite = new HermiteRuleFactory();

    /**
     * Creates a Gauss-Legendre integrator of the given order.
     * The call to the
     * {@link GaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method will perform an integration on the natural interval
     * {@code [-1 , 1]}.
     *
     * @param numberOfPoints Order of the integration rule.
     * @return a Gauss-Legendre integrator.
     */
    public GaussIntegrator legendre(int numberOfPoints) {
        return new GaussIntegrator(getRule(legendre, numberOfPoints));
    }

    /**
     * Creates a Gauss-Legendre integrator of the given order.
     * The call to the
     * {@link GaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method will perform an integration on the given interval.
     *
     * @param numberOfPoints Order of the integration rule.
     * @param lowerBound Lower bound of the integration interval.
     * @param upperBound Upper bound of the integration interval.
     * @return a Gauss-Legendre integrator.
     * @throws NotStrictlyPositiveException if number of points is not positive
     */
    public GaussIntegrator legendre(int numberOfPoints,
                                    double lowerBound,
                                    double upperBound)
        throws NotStrictlyPositiveException {
        return new GaussIntegrator(transform(getRule(legendre, numberOfPoints),
                                             lowerBound, upperBound));
    }

    /**
     * Creates a Gauss-Legendre integrator of the given order.
     * The call to the
     * {@link GaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method will perform an integration on the natural interval
     * {@code [-1 , 1]}.
     *
     * @param numberOfPoints Order of the integration rule.
     * @return a Gauss-Legendre integrator.
     * @throws NotStrictlyPositiveException if number of points is not positive
     */
    public GaussIntegrator legendreHighPrecision(int numberOfPoints)
        throws NotStrictlyPositiveException {
        return new GaussIntegrator(getRule(legendreHighPrecision, numberOfPoints));
    }

    /**
     * Creates an integrator of the given order, and whose call to the
     * {@link GaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method will perform an integration on the given interval.
     *
     * @param numberOfPoints Order of the integration rule.
     * @param lowerBound Lower bound of the integration interval.
     * @param upperBound Upper bound of the integration interval.
     * @return a Gauss-Legendre integrator.
     * @throws NotStrictlyPositiveException if number of points is not positive
     */
    public GaussIntegrator legendreHighPrecision(int numberOfPoints,
                                                 double lowerBound,
                                                 double upperBound)
        throws NotStrictlyPositiveException {
        return new GaussIntegrator(transform(getRule(legendreHighPrecision, numberOfPoints),
                                             lowerBound, upperBound));
    }

    /**
     * Creates a Gauss-Hermite integrator of the given order.
     * The call to the
     * {@link SymmetricGaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method will perform a weighted integration on the interval
     * \([-\infty, +\infty]\): the computed value is the improper integral of
     * \(e^{-x^2}f(x)\)
     * where \(f(x)\) is the function passed to the
     * {@link SymmetricGaussIntegrator#integrate(org.apache.commons.math3.analysis.UnivariateFunction)
     * integrate} method.
     *
     * @param numberOfPoints Order of the integration rule.
     * @return a Gauss-Hermite integrator.
     */
    public SymmetricGaussIntegrator hermite(int numberOfPoints) {
        return new SymmetricGaussIntegrator(getRule(hermite, numberOfPoints));
    }

    /**
     * @param factory Integration rule factory.
     * @param numberOfPoints Order of the integration rule.
     * @return the integration nodes and weights.
     * @throws NotStrictlyPositiveException if number of points is not positive
     * @throws DimensionMismatchException if the elements of the rule pair do not
     * have the same length.
     */
    private static Pair<double[], double[]> getRule(BaseRuleFactory<? extends Number> factory,
                                                    int numberOfPoints)
        throws NotStrictlyPositiveException, DimensionMismatchException {
        return factory.getRule(numberOfPoints);
    }

    /**
     * Performs a change of variable so that the integration can be performed
     * on an arbitrary interval {@code [a, b]}.
     * It is assumed that the natural interval is {@code [-1, 1]}.
     *
     * @param rule Original points and weights.
     * @param a Lower bound of the integration interval.
     * @param b Lower bound of the integration interval.
     * @return the points and weights adapted to the new interval.
     */
    private static Pair<double[], double[]> transform(Pair<double[], double[]> rule,
                                                      double a,
                                                      double b) {
        final double[] points = rule.getFirst();
        final double[] weights = rule.getSecond();

        // Scaling
        final double scale = (b - a) / 2;
        final double shift = a + scale;

        for (int i = 0; i < points.length; i++) {
            points[i] = points[i] * scale + shift;
            weights[i] *= scale;
        }

        return new Pair<double[], double[]>(points, weights);
    }
}
