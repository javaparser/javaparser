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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.apache.commons.math3.analysis.function.HarmonicOscillator;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresBuilder;
import org.apache.commons.math3.fitting.leastsquares.LeastSquaresProblem;
import org.apache.commons.math3.linear.DiagonalMatrix;
import org.apache.commons.math3.util.FastMath;

/**
 * Fits points to a {@link
 * org.apache.commons.math3.analysis.function.HarmonicOscillator.Parametric harmonic oscillator}
 * function.
 * <br/>
 * The {@link #withStartPoint(double[]) initial guess values} must be passed
 * in the following order:
 * <ul>
 *  <li>Amplitude</li>
 *  <li>Angular frequency</li>
 *  <li>phase</li>
 * </ul>
 * The optimal values will be returned in the same order.
 *
 * @since 3.3
 */
public class HarmonicCurveFitter extends AbstractCurveFitter {
    /** Parametric function to be fitted. */
    private static final HarmonicOscillator.Parametric FUNCTION = new HarmonicOscillator.Parametric();
    /** Initial guess. */
    private final double[] initialGuess;
    /** Maximum number of iterations of the optimization algorithm. */
    private final int maxIter;

    /**
     * Contructor used by the factory methods.
     *
     * @param initialGuess Initial guess. If set to {@code null}, the initial guess
     * will be estimated using the {@link ParameterGuesser}.
     * @param maxIter Maximum number of iterations of the optimization algorithm.
     */
    private HarmonicCurveFitter(double[] initialGuess,
                                int maxIter) {
        this.initialGuess = initialGuess;
        this.maxIter = maxIter;
    }

    /**
     * Creates a default curve fitter.
     * The initial guess for the parameters will be {@link ParameterGuesser}
     * computed automatically, and the maximum number of iterations of the
     * optimization algorithm is set to {@link Integer#MAX_VALUE}.
     *
     * @return a curve fitter.
     *
     * @see #withStartPoint(double[])
     * @see #withMaxIterations(int)
     */
    public static HarmonicCurveFitter create() {
        return new HarmonicCurveFitter(null, Integer.MAX_VALUE);
    }

    /**
     * Configure the start point (initial guess).
     * @param newStart new start point (initial guess)
     * @return a new instance.
     */
    public HarmonicCurveFitter withStartPoint(double[] newStart) {
        return new HarmonicCurveFitter(newStart.clone(),
                                       maxIter);
    }

    /**
     * Configure the maximum number of iterations.
     * @param newMaxIter maximum number of iterations
     * @return a new instance.
     */
    public HarmonicCurveFitter withMaxIterations(int newMaxIter) {
        return new HarmonicCurveFitter(initialGuess,
                                       newMaxIter);
    }

    /** {@inheritDoc} */
    @Override
    protected LeastSquaresProblem getProblem(Collection<WeightedObservedPoint> observations) {
        // Prepare least-squares problem.
        final int len = observations.size();
        final double[] target  = new double[len];
        final double[] weights = new double[len];

        int i = 0;
        for (WeightedObservedPoint obs : observations) {
            target[i]  = obs.getY();
            weights[i] = obs.getWeight();
            ++i;
        }

        final AbstractCurveFitter.TheoreticalValuesFunction model
            = new AbstractCurveFitter.TheoreticalValuesFunction(FUNCTION,
                                                                observations);

        final double[] startPoint = initialGuess != null ?
            initialGuess :
            // Compute estimation.
            new ParameterGuesser(observations).guess();

        // Return a new optimizer set up to fit a Gaussian curve to the
        // observed points.
        return new LeastSquaresBuilder().
                maxEvaluations(Integer.MAX_VALUE).
                maxIterations(maxIter).
                start(startPoint).
                target(target).
                weight(new DiagonalMatrix(weights)).
                model(model.getModelFunction(), model.getModelFunctionJacobian()).
                build();

    }

    /**
     * This class guesses harmonic coefficients from a sample.
     * <p>The algorithm used to guess the coefficients is as follows:</p>
     *
     * <p>We know \( f(t) \) at some sampling points \( t_i \) and want
     * to find \( a \), \( \omega \) and \( \phi \) such that
     * \( f(t) = a \cos (\omega t + \phi) \).
     * </p>
     *
     * <p>From the analytical expression, we can compute two primitives :
     * \[
     *     If2(t) = \int f^2 dt  = a^2 (t + S(t)) / 2
     * \]
     * \[
     *     If'2(t) = \int f'^2 dt = a^2 \omega^2 (t - S(t)) / 2
     * \]
     * where \(S(t) = \frac{\sin(2 (\omega t + \phi))}{2\omega}\)
     * </p>
     *
     * <p>We can remove \(S\) between these expressions :
     * \[
     *     If'2(t) = a^2 \omega^2 t - \omega^2 If2(t)
     * \]
     * </p>
     *
     * <p>The preceding expression shows that \(If'2 (t)\) is a linear
     * combination of both \(t\) and \(If2(t)\):
     * \[
     *   If'2(t) = A t + B If2(t)
     * \]
     * </p>
     *
     * <p>From the primitive, we can deduce the same form for definite
     * integrals between \(t_1\) and \(t_i\) for each \(t_i\) :
     * \[
     *   If2(t_i) - If2(t_1) = A (t_i - t_1) + B (If2 (t_i) - If2(t_1))
     * \]
     * </p>
     *
     * <p>We can find the coefficients \(A\) and \(B\) that best fit the sample
     * to this linear expression by computing the definite integrals for
     * each sample points.
     * </p>
     *
     * <p>For a bilinear expression \(z(x_i, y_i) = A x_i + B y_i\), the
     * coefficients \(A\) and \(B\) that minimize a least-squares criterion
     * \(\sum (z_i - z(x_i, y_i))^2\) are given by these expressions:</p>
     * \[
     *   A = \frac{\sum y_i y_i \sum x_i z_i - \sum x_i y_i \sum y_i z_i}
     *            {\sum x_i x_i \sum y_i y_i - \sum x_i y_i \sum x_i y_i}
     * \]
     * \[
     *   B = \frac{\sum x_i x_i \sum y_i z_i - \sum x_i y_i \sum x_i z_i}
     *            {\sum x_i x_i \sum y_i y_i - \sum x_i y_i \sum x_i y_i}
     *
     * \]
     *
     * <p>In fact, we can assume that both \(a\) and \(\omega\) are positive and
     * compute them directly, knowing that \(A = a^2 \omega^2\) and that
     * \(B = -\omega^2\). The complete algorithm is therefore:</p>
     *
     * For each \(t_i\) from \(t_1\) to \(t_{n-1}\), compute:
     * \[ f(t_i) \]
     * \[ f'(t_i) = \frac{f (t_{i+1}) - f(t_{i-1})}{t_{i+1} - t_{i-1}} \]
     * \[ x_i = t_i  - t_1 \]
     * \[ y_i = \int_{t_1}^{t_i} f^2(t) dt \]
     * \[ z_i = \int_{t_1}^{t_i} f'^2(t) dt \]
     * and update the sums:
     * \[ \sum x_i x_i, \sum y_i y_i, \sum x_i y_i, \sum x_i z_i, \sum y_i z_i \]
     *
     * Then:
     * \[
     *  a = \sqrt{\frac{\sum y_i y_i  \sum x_i z_i - \sum x_i y_i \sum y_i z_i }
     *                 {\sum x_i y_i  \sum x_i z_i - \sum x_i x_i \sum y_i z_i }}
     * \]
     * \[
     *  \omega = \sqrt{\frac{\sum x_i y_i \sum x_i z_i - \sum x_i x_i \sum y_i z_i}
     *                      {\sum x_i x_i \sum y_i y_i - \sum x_i y_i \sum x_i y_i}}
     * \]
     *
     * <p>Once we know \(\omega\) we can compute:
     * \[
     *    fc = \omega f(t) \cos(\omega t) - f'(t) \sin(\omega t)
     * \]
     * \[
     *    fs = \omega f(t) \sin(\omega t) + f'(t) \cos(\omega t)
     * \]
     * </p>
     *
     * <p>It appears that \(fc = a \omega \cos(\phi)\) and
     * \(fs = -a \omega \sin(\phi)\), so we can use these
     * expressions to compute \(\phi\). The best estimate over the sample is
     * given by averaging these expressions.
     * </p>
     *
     * <p>Since integrals and means are involved in the preceding
     * estimations, these operations run in \(O(n)\) time, where \(n\) is the
     * number of measurements.</p>
     */
    public static class ParameterGuesser {
        /** Amplitude. */
        private final double a;
        /** Angular frequency. */
        private final double omega;
        /** Phase. */
        private final double phi;

        /**
         * Simple constructor.
         *
         * @param observations Sampled observations.
         * @throws NumberIsTooSmallException if the sample is too short.
         * @throws ZeroException if the abscissa range is zero.
         * @throws MathIllegalStateException when the guessing procedure cannot
         * produce sensible results.
         */
        public ParameterGuesser(Collection<WeightedObservedPoint> observations) {
            if (observations.size() < 4) {
                throw new NumberIsTooSmallException(LocalizedFormats.INSUFFICIENT_OBSERVED_POINTS_IN_SAMPLE,
                                                    observations.size(), 4, true);
            }

            final WeightedObservedPoint[] sorted
                = sortObservations(observations).toArray(new WeightedObservedPoint[0]);

            final double aOmega[] = guessAOmega(sorted);
            a = aOmega[0];
            omega = aOmega[1];

            phi = guessPhi(sorted);
        }

        /**
         * Gets an estimation of the parameters.
         *
         * @return the guessed parameters, in the following order:
         * <ul>
         *  <li>Amplitude</li>
         *  <li>Angular frequency</li>
         *  <li>Phase</li>
         * </ul>
         */
        public double[] guess() {
            return new double[] { a, omega, phi };
        }

        /**
         * Sort the observations with respect to the abscissa.
         *
         * @param unsorted Input observations.
         * @return the input observations, sorted.
         */
        private List<WeightedObservedPoint> sortObservations(Collection<WeightedObservedPoint> unsorted) {
            final List<WeightedObservedPoint> observations = new ArrayList<WeightedObservedPoint>(unsorted);

            // Since the samples are almost always already sorted, this
            // method is implemented as an insertion sort that reorders the
            // elements in place. Insertion sort is very efficient in this case.
            WeightedObservedPoint curr = observations.get(0);
            final int len = observations.size();
            for (int j = 1; j < len; j++) {
                WeightedObservedPoint prec = curr;
                curr = observations.get(j);
                if (curr.getX() < prec.getX()) {
                    // the current element should be inserted closer to the beginning
                    int i = j - 1;
                    WeightedObservedPoint mI = observations.get(i);
                    while ((i >= 0) && (curr.getX() < mI.getX())) {
                        observations.set(i + 1, mI);
                        if (i-- != 0) {
                            mI = observations.get(i);
                        }
                    }
                    observations.set(i + 1, curr);
                    curr = observations.get(j);
                }
            }

            return observations;
        }

        /**
         * Estimate a first guess of the amplitude and angular frequency.
         *
         * @param observations Observations, sorted w.r.t. abscissa.
         * @throws ZeroException if the abscissa range is zero.
         * @throws MathIllegalStateException when the guessing procedure cannot
         * produce sensible results.
         * @return the guessed amplitude (at index 0) and circular frequency
         * (at index 1).
         */
        private double[] guessAOmega(WeightedObservedPoint[] observations) {
            final double[] aOmega = new double[2];

            // initialize the sums for the linear model between the two integrals
            double sx2 = 0;
            double sy2 = 0;
            double sxy = 0;
            double sxz = 0;
            double syz = 0;

            double currentX = observations[0].getX();
            double currentY = observations[0].getY();
            double f2Integral = 0;
            double fPrime2Integral = 0;
            final double startX = currentX;
            for (int i = 1; i < observations.length; ++i) {
                // one step forward
                final double previousX = currentX;
                final double previousY = currentY;
                currentX = observations[i].getX();
                currentY = observations[i].getY();

                // update the integrals of f<sup>2</sup> and f'<sup>2</sup>
                // considering a linear model for f (and therefore constant f')
                final double dx = currentX - previousX;
                final double dy = currentY - previousY;
                final double f2StepIntegral =
                    dx * (previousY * previousY + previousY * currentY + currentY * currentY) / 3;
                final double fPrime2StepIntegral = dy * dy / dx;

                final double x = currentX - startX;
                f2Integral += f2StepIntegral;
                fPrime2Integral += fPrime2StepIntegral;

                sx2 += x * x;
                sy2 += f2Integral * f2Integral;
                sxy += x * f2Integral;
                sxz += x * fPrime2Integral;
                syz += f2Integral * fPrime2Integral;
            }

            // compute the amplitude and pulsation coefficients
            double c1 = sy2 * sxz - sxy * syz;
            double c2 = sxy * sxz - sx2 * syz;
            double c3 = sx2 * sy2 - sxy * sxy;
            if ((c1 / c2 < 0) || (c2 / c3 < 0)) {
                final int last = observations.length - 1;
                // Range of the observations, assuming that the
                // observations are sorted.
                final double xRange = observations[last].getX() - observations[0].getX();
                if (xRange == 0) {
                    throw new ZeroException();
                }
                aOmega[1] = 2 * Math.PI / xRange;

                double yMin = Double.POSITIVE_INFINITY;
                double yMax = Double.NEGATIVE_INFINITY;
                for (int i = 1; i < observations.length; ++i) {
                    final double y = observations[i].getY();
                    if (y < yMin) {
                        yMin = y;
                    }
                    if (y > yMax) {
                        yMax = y;
                    }
                }
                aOmega[0] = 0.5 * (yMax - yMin);
            } else {
                if (c2 == 0) {
                    // In some ill-conditioned cases (cf. MATH-844), the guesser
                    // procedure cannot produce sensible results.
                    throw new MathIllegalStateException(LocalizedFormats.ZERO_DENOMINATOR);
                }

                aOmega[0] = FastMath.sqrt(c1 / c2);
                aOmega[1] = FastMath.sqrt(c2 / c3);
            }

            return aOmega;
        }

        /**
         * Estimate a first guess of the phase.
         *
         * @param observations Observations, sorted w.r.t. abscissa.
         * @return the guessed phase.
         */
        private double guessPhi(WeightedObservedPoint[] observations) {
            // initialize the means
            double fcMean = 0;
            double fsMean = 0;

            double currentX = observations[0].getX();
            double currentY = observations[0].getY();
            for (int i = 1; i < observations.length; ++i) {
                // one step forward
                final double previousX = currentX;
                final double previousY = currentY;
                currentX = observations[i].getX();
                currentY = observations[i].getY();
                final double currentYPrime = (currentY - previousY) / (currentX - previousX);

                double omegaX = omega * currentX;
                double cosine = FastMath.cos(omegaX);
                double sine = FastMath.sin(omegaX);
                fcMean += omega * currentY * cosine - currentYPrime * sine;
                fsMean += omega * currentY * sine + currentYPrime * cosine;
            }

            return FastMath.atan2(-fsMean, fcMean);
        }
    }
}
