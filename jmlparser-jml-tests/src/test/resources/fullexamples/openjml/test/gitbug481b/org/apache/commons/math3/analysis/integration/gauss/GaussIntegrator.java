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

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NonMonotonicSequenceException;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.Pair;

/**
 * Class that implements the Gaussian rule for
 * {@link #integrate(UnivariateFunction) integrating} a weighted
 * function.
 *
 * @since 3.1
 */
public class GaussIntegrator {
    /** Nodes. */
    private final double[] points;
    /** Nodes weights. */
    private final double[] weights;

    /**
     * Creates an integrator from the given {@code points} and {@code weights}.
     * The integration interval is defined by the first and last value of
     * {@code points} which must be sorted in increasing order.
     *
     * @param points Integration points.
     * @param weights Weights of the corresponding integration nodes.
     * @throws NonMonotonicSequenceException if the {@code points} are not
     * sorted in increasing order.
     * @throws DimensionMismatchException if points and weights don't have the same length
     */
    public GaussIntegrator(double[] points,
                           double[] weights)
        throws NonMonotonicSequenceException, DimensionMismatchException {
        if (points.length != weights.length) {
            throw new DimensionMismatchException(points.length,
                                                 weights.length);
        }

        MathArrays.checkOrder(points, MathArrays.OrderDirection.INCREASING, true, true);

        this.points = points.clone();
        this.weights = weights.clone();
    }

    /**
     * Creates an integrator from the given pair of points (first element of
     * the pair) and weights (second element of the pair.
     *
     * @param pointsAndWeights Integration points and corresponding weights.
     * @throws NonMonotonicSequenceException if the {@code points} are not
     * sorted in increasing order.
     *
     * @see #GaussIntegrator(double[], double[])
     */
    public GaussIntegrator(Pair<double[], double[]> pointsAndWeights)
        throws NonMonotonicSequenceException {
        this(pointsAndWeights.getFirst(), pointsAndWeights.getSecond());
    }

    /**
     * Returns an estimate of the integral of {@code f(x) * w(x)},
     * where {@code w} is a weight function that depends on the actual
     * flavor of the Gauss integration scheme.
     * The algorithm uses the points and associated weights, as passed
     * to the {@link #GaussIntegrator(double[],double[]) constructor}.
     *
     * @param f Function to integrate.
     * @return the integral of the weighted function.
     */
    public double integrate(UnivariateFunction f) {
        double s = 0;
        double c = 0;
        for (int i = 0; i < points.length; i++) {
            final double x = points[i];
            final double w = weights[i];
            final double y = w * f.value(x) - c;
            final double t = s + y;
            c = (t - s) - y;
            s = t;
        }
        return s;
    }

    /**
     * @return the order of the integration rule (the number of integration
     * points).
     */
    public int getNumberOfPoints() {
        return points.length;
    }

    /**
     * Gets the integration point at the given index.
     * The index must be in the valid range but no check is performed.
     * @param index index of the integration point
     * @return the integration point.
     */
    public double getPoint(int index) {
        return points[index];
    }

    /**
     * Gets the weight of the integration point at the given index.
     * The index must be in the valid range but no check is performed.
     * @param index index of the integration point
     * @return the weight.
     */
    public double getWeight(int index) {
        return weights[index];
    }
}
