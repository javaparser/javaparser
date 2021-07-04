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
package org.apache.commons.math3.fitting;

import java.util.Arrays;
import java.util.Comparator;
import org.apache.commons.math3.analysis.function.Gaussian;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.optim.nonlinear.vector.MultivariateVectorOptimizer;
import org.apache.commons.math3.util.FastMath;

/**
 * Fits points to a {@link
 * org.apache.commons.math3.analysis.function.Gaussian.Parametric Gaussian} function.
 * <p>
 * Usage example:
 * <pre>
 *   GaussianFitter fitter = new GaussianFitter(
 *     new LevenbergMarquardtOptimizer());
 *   fitter.addObservedPoint(4.0254623,  531026.0);
 *   fitter.addObservedPoint(4.03128248, 984167.0);
 *   fitter.addObservedPoint(4.03839603, 1887233.0);
 *   fitter.addObservedPoint(4.04421621, 2687152.0);
 *   fitter.addObservedPoint(4.05132976, 3461228.0);
 *   fitter.addObservedPoint(4.05326982, 3580526.0);
 *   fitter.addObservedPoint(4.05779662, 3439750.0);
 *   fitter.addObservedPoint(4.0636168,  2877648.0);
 *   fitter.addObservedPoint(4.06943698, 2175960.0);
 *   fitter.addObservedPoint(4.07525716, 1447024.0);
 *   fitter.addObservedPoint(4.08237071, 717104.0);
 *   fitter.addObservedPoint(4.08366408, 620014.0);
 *   double[] parameters = fitter.fit();
 * </pre>
 *
 * @since 2.2
 * @deprecated As of 3.3. Please use {@link GaussianCurveFitter} and
 * {@link WeightedObservedPoints} instead.
 */
@Deprecated
public class GaussianFitter extends CurveFitter<Gaussian.Parametric> {
    /**
     * Constructs an instance using the specified optimizer.
     *
     * @param optimizer Optimizer to use for the fitting.
     */
    public GaussianFitter(MultivariateVectorOptimizer optimizer) {
        super(optimizer);
    }

    /**
     * Fits a Gaussian function to the observed points.
     *
     * @param initialGuess First guess values in the following order:
     * <ul>
     *  <li>Norm</li>
     *  <li>Mean</li>
     *  <li>Sigma</li>
     * </ul>
     * @return the parameters of the Gaussian function that best fits the
     * observed points (in the same order as above).
     * @since 3.0
     */
    public double[] fit(double[] initialGuess) {
        final Gaussian.Parametric f = new Gaussian.Parametric() {
                /** {@inheritDoc} */
                @Override
                public double value(double x, double ... p) {
                    double v = Double.POSITIVE_INFINITY;
                    try {
                        v = super.value(x, p);
                    } catch (NotStrictlyPositiveException e) { // NOPMD
                        // Do nothing.
                    }
                    return v;
                }

                /** {@inheritDoc} */
                @Override
                public double[] gradient(double x, double ... p) {
                    double[] v = { Double.POSITIVE_INFINITY,
                                   Double.POSITIVE_INFINITY,
                                   Double.POSITIVE_INFINITY };
                    try {
                        v = super.gradient(x, p);
                    } catch (NotStrictlyPositiveException e) { // NOPMD
                        // Do nothing.
                    }
                    return v;
                }
            };

        return fit(f, initialGuess);
    }

    /**
     * Fits a Gaussian function to the observed points.
     *
     * @return the parameters of the Gaussian function that best fits the
     * observed points (in the same order as above).
     */
    public double[] fit() {
        final double[] guess = (new ParameterGuesser(getObservations())).guess();
        return fit(guess);
    }

    /**
     * Guesses the parameters {@code norm}, {@code mean}, and {@code sigma}
     * of a {@link org.apache.commons.math3.analysis.function.Gaussian.Parametric}
     * based on the specified observed points.
     */
    public static class ParameterGuesser {
        /** Normalization factor. */
        private final double norm;
        /** Mean. */
        private final double mean;
        /** Standard deviation. */
        private final double sigma;

        /**
         * Constructs instance with the specified observed points.
         *
         * @param observations Observed points from which to guess the
         * parameters of the Gaussian.
         * @throws NullArgumentException if {@code observations} is
         * {@code null}.
         * @throws NumberIsTooSmallException if there are less than 3
         * observations.
         */
        public ParameterGuesser(WeightedObservedPoint[] observations) {
            if (observations == null) {
                throw new NullArgumentException(LocalizedFormats.INPUT_ARRAY);
            }
            if (observations.length < 3) {
                throw new NumberIsTooSmallException(observations.length, 3, true);
            }

            final WeightedObservedPoint[] sorted = sortObservations(observations);
            final double[] params = basicGuess(sorted);

            norm = params[0];
            mean = params[1];
            sigma = params[2];
        }

        /**
         * Gets an estimation of the parameters.
         *
         * @return the guessed parameters, in the following order:
         * <ul>
         *  <li>Normalization factor</li>
         *  <li>Mean</li>
         *  <li>Standard deviation</li>
         * </ul>
         */
        public double[] guess() {
            return new double[] { norm, mean, sigma };
        }

        /**
         * Sort the observations.
         *
         * @param unsorted Input observations.
         * @return the input observations, sorted.
         */
        private WeightedObservedPoint[] sortObservations(WeightedObservedPoint[] unsorted) {
            final WeightedObservedPoint[] observations = unsorted.clone();
            final Comparator<WeightedObservedPoint> cmp
                = new Comparator<WeightedObservedPoint>() {
                /** {@inheritDoc} */
                public int compare(WeightedObservedPoint p1,
                                   WeightedObservedPoint p2) {
                    if (p1 == null && p2 == null) {
                        return 0;
                    }
                    if (p1 == null) {
                        return -1;
                    }
                    if (p2 == null) {
                        return 1;
                    }
                    final int cmpX = Double.compare(p1.getX(), p2.getX());
                    if (cmpX < 0) {
                        return -1;
                    }
                    if (cmpX > 0) {
                        return 1;
                    }
                    final int cmpY = Double.compare(p1.getY(), p2.getY());
                    if (cmpY < 0) {
                        return -1;
                    }
                    if (cmpY > 0) {
                        return 1;
                    }
                    final int cmpW = Double.compare(p1.getWeight(), p2.getWeight());
                    if (cmpW < 0) {
                        return -1;
                    }
                    if (cmpW > 0) {
                        return 1;
                    }
                    return 0;
                }
            };

            Arrays.sort(observations, cmp);
            return observations;
        }

        /**
         * Guesses the parameters based on the specified observed points.
         *
         * @param points Observed points, sorted.
         * @return the guessed parameters (normalization factor, mean and
         * sigma).
         */
        private double[] basicGuess(WeightedObservedPoint[] points) {
            final int maxYIdx = findMaxY(points);
            final double n = points[maxYIdx].getY();
            final double m = points[maxYIdx].getX();

            double fwhmApprox;
            try {
                final double halfY = n + ((m - n) / 2);
                final double fwhmX1 = interpolateXAtY(points, maxYIdx, -1, halfY);
                final double fwhmX2 = interpolateXAtY(points, maxYIdx, 1, halfY);
                fwhmApprox = fwhmX2 - fwhmX1;
            } catch (OutOfRangeException e) {
                // TODO: Exceptions should not be used for flow control.
                fwhmApprox = points[points.length - 1].getX() - points[0].getX();
            }
            final double s = fwhmApprox / (2 * FastMath.sqrt(2 * FastMath.log(2)));

            return new double[] { n, m, s };
        }

        /**
         * Finds index of point in specified points with the largest Y.
         *
         * @param points Points to search.
         * @return the index in specified points array.
         */
        private int findMaxY(WeightedObservedPoint[] points) {
            int maxYIdx = 0;
            for (int i = 1; i < points.length; i++) {
                if (points[i].getY() > points[maxYIdx].getY()) {
                    maxYIdx = i;
                }
            }
            return maxYIdx;
        }

        /**
         * Interpolates using the specified points to determine X at the
         * specified Y.
         *
         * @param points Points to use for interpolation.
         * @param startIdx Index within points from which to start the search for
         * interpolation bounds points.
         * @param idxStep Index step for searching interpolation bounds points.
         * @param y Y value for which X should be determined.
         * @return the value of X for the specified Y.
         * @throws ZeroException if {@code idxStep} is 0.
         * @throws OutOfRangeException if specified {@code y} is not within the
         * range of the specified {@code points}.
         */
        private double interpolateXAtY(WeightedObservedPoint[] points,
                                       int startIdx,
                                       int idxStep,
                                       double y)
            throws OutOfRangeException {
            if (idxStep == 0) {
                throw new ZeroException();
            }
            final WeightedObservedPoint[] twoPoints
                = getInterpolationPointsForY(points, startIdx, idxStep, y);
            final WeightedObservedPoint p1 = twoPoints[0];
            final WeightedObservedPoint p2 = twoPoints[1];
            if (p1.getY() == y) {
                return p1.getX();
            }
            if (p2.getY() == y) {
                return p2.getX();
            }
            return p1.getX() + (((y - p1.getY()) * (p2.getX() - p1.getX())) /
                                (p2.getY() - p1.getY()));
        }

        /**
         * Gets the two bounding interpolation points from the specified points
         * suitable for determining X at the specified Y.
         *
         * @param points Points to use for interpolation.
         * @param startIdx Index within points from which to start search for
         * interpolation bounds points.
         * @param idxStep Index step for search for interpolation bounds points.
         * @param y Y value for which X should be determined.
         * @return the array containing two points suitable for determining X at
         * the specified Y.
         * @throws ZeroException if {@code idxStep} is 0.
         * @throws OutOfRangeException if specified {@code y} is not within the
         * range of the specified {@code points}.
         */
        private WeightedObservedPoint[] getInterpolationPointsForY(WeightedObservedPoint[] points,
                                                                   int startIdx,
                                                                   int idxStep,
                                                                   double y)
            throws OutOfRangeException {
            if (idxStep == 0) {
                throw new ZeroException();
            }
            for (int i = startIdx;
                 idxStep < 0 ? i + idxStep >= 0 : i + idxStep < points.length;
                 i += idxStep) {
                final WeightedObservedPoint p1 = points[i];
                final WeightedObservedPoint p2 = points[i + idxStep];
                if (isBetween(y, p1.getY(), p2.getY())) {
                    if (idxStep < 0) {
                        return new WeightedObservedPoint[] { p2, p1 };
                    } else {
                        return new WeightedObservedPoint[] { p1, p2 };
                    }
                }
            }

            // Boundaries are replaced by dummy values because the raised
            // exception is caught and the message never displayed.
            // TODO: Exceptions should not be used for flow control.
            throw new OutOfRangeException(y,
                                          Double.NEGATIVE_INFINITY,
                                          Double.POSITIVE_INFINITY);
        }

        /**
         * Determines whether a value is between two other values.
         *
         * @param value Value to test whether it is between {@code boundary1}
         * and {@code boundary2}.
         * @param boundary1 One end of the range.
         * @param boundary2 Other end of the range.
         * @return {@code true} if {@code value} is between {@code boundary1} and
         * {@code boundary2} (inclusive), {@code false} otherwise.
         */
        private boolean isBetween(double value,
                                  double boundary1,
                                  double boundary2) {
            return (value >= boundary1 && value <= boundary2) ||
                (value >= boundary2 && value <= boundary1);
        }
    }
}
