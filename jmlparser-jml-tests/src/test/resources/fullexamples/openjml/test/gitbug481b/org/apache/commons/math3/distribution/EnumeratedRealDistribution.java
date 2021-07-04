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
package org.apache.commons.math3.distribution;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.NotANumberException;
import org.apache.commons.math3.exception.NotFiniteNumberException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.random.Well19937c;
import org.apache.commons.math3.util.Pair;

/**
 * <p>Implementation of a real-valued {@link EnumeratedDistribution}.
 *
 * <p>Values with zero-probability are allowed but they do not extend the
 * support.<br/>
 * Duplicate values are allowed. Probabilities of duplicate values are combined
 * when computing cumulative probabilities and statistics.</p>
 *
 * @since 3.2
 */
public class EnumeratedRealDistribution extends AbstractRealDistribution {

    /** Serializable UID. */
    private static final long serialVersionUID = 20130308L;

    /**
     * {@link EnumeratedDistribution} (using the {@link Double} wrapper)
     * used to generate the pmf.
     */
    protected final EnumeratedDistribution<Double> innerDistribution;

    /**
     * Create a discrete real-valued distribution using the given probability mass function
     * enumeration.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link Well19937c} as random generator to be used for sampling only (see
     * {@link #sample()} and {@link #sample(int)}). In case no sampling is
     * needed for the created distribution, it is advised to pass {@code null}
     * as random generator via the appropriate constructors to avoid the
     * additional initialisation overhead.
     *
     * @param singletons array of random variable values.
     * @param probabilities array of probabilities.
     * @throws DimensionMismatchException if
     * {@code singletons.length != probabilities.length}
     * @throws NotPositiveException if any of the probabilities are negative.
     * @throws NotFiniteNumberException if any of the probabilities are infinite.
     * @throws NotANumberException if any of the probabilities are NaN.
     * @throws MathArithmeticException all of the probabilities are 0.
     */
    public EnumeratedRealDistribution(final double[] singletons, final double[] probabilities)
    throws DimensionMismatchException, NotPositiveException, MathArithmeticException,
           NotFiniteNumberException, NotANumberException {
        this(new Well19937c(), singletons, probabilities);
    }

    /**
     * Create a discrete real-valued distribution using the given random number generator
     * and probability mass function enumeration.
     *
     * @param rng random number generator.
     * @param singletons array of random variable values.
     * @param probabilities array of probabilities.
     * @throws DimensionMismatchException if
     * {@code singletons.length != probabilities.length}
     * @throws NotPositiveException if any of the probabilities are negative.
     * @throws NotFiniteNumberException if any of the probabilities are infinite.
     * @throws NotANumberException if any of the probabilities are NaN.
     * @throws MathArithmeticException all of the probabilities are 0.
     */
    public EnumeratedRealDistribution(final RandomGenerator rng,
                                    final double[] singletons, final double[] probabilities)
        throws DimensionMismatchException, NotPositiveException, MathArithmeticException,
               NotFiniteNumberException, NotANumberException {
        super(rng);

        innerDistribution = new EnumeratedDistribution<Double>(
                rng, createDistribution(singletons, probabilities));
    }

    /**
     * Create a discrete real-valued distribution from the input data.  Values are assigned
     * mass based on their frequency.
     *
     * @param rng random number generator used for sampling
     * @param data input dataset
     * @since 3.6
     */
    public EnumeratedRealDistribution(final RandomGenerator rng, final double[] data) {
        super(rng);
        final Map<Double, Integer> dataMap = new HashMap<Double, Integer>();
        for (double value : data) {
            Integer count = dataMap.get(value);
            if (count == null) {
                count = 0;
            }
            dataMap.put(value, ++count);
        }
        final int massPoints = dataMap.size();
        final double denom = data.length;
        final double[] values = new double[massPoints];
        final double[] probabilities = new double[massPoints];
        int index = 0;
        for (Entry<Double, Integer> entry : dataMap.entrySet()) {
            values[index] = entry.getKey();
            probabilities[index] = entry.getValue().intValue() / denom;
            index++;
        }
        innerDistribution = new EnumeratedDistribution<Double>(rng, createDistribution(values, probabilities));
    }

    /**
     * Create a discrete real-valued distribution from the input data.  Values are assigned
     * mass based on their frequency.  For example, [0,1,1,2] as input creates a distribution
     * with values 0, 1 and 2 having probability masses 0.25, 0.5 and 0.25 respectively,
     *
     * @param data input dataset
     * @since 3.6
     */
    public EnumeratedRealDistribution(final double[] data) {
        this(new Well19937c(), data);
    }
    /**
     * Create the list of Pairs representing the distribution from singletons and probabilities.
     *
     * @param singletons values
     * @param probabilities probabilities
     * @return list of value/probability pairs
     */
    private static List<Pair<Double, Double>>  createDistribution(double[] singletons, double[] probabilities) {
        if (singletons.length != probabilities.length) {
            throw new DimensionMismatchException(probabilities.length, singletons.length);
        }

        final List<Pair<Double, Double>> samples = new ArrayList<Pair<Double, Double>>(singletons.length);

        for (int i = 0; i < singletons.length; i++) {
            samples.add(new Pair<Double, Double>(singletons[i], probabilities[i]));
        }
        return samples;

    }

    /**
     * {@inheritDoc}
     */
    @Override
    public double probability(final double x) {
        return innerDistribution.probability(x);
    }

    /**
     * For a random variable {@code X} whose values are distributed according to
     * this distribution, this method returns {@code P(X = x)}. In other words,
     * this method represents the probability mass function (PMF) for the
     * distribution.
     *
     * @param x the point at which the PMF is evaluated
     * @return the value of the probability mass function at point {@code x}
     */
    public double density(final double x) {
        return probability(x);
    }

    /**
     * {@inheritDoc}
     */
    public double cumulativeProbability(final double x) {
        double probability = 0;

        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            if (sample.getKey() <= x) {
                probability += sample.getValue();
            }
        }

        return probability;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public double inverseCumulativeProbability(final double p) throws OutOfRangeException {
        if (p < 0.0 || p > 1.0) {
            throw new OutOfRangeException(p, 0, 1);
        }

        double probability = 0;
        double x = getSupportLowerBound();
        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            if (sample.getValue() == 0.0) {
                continue;
            }

            probability += sample.getValue();
            x = sample.getKey();

            if (probability >= p) {
                break;
            }
        }

        return x;
    }

    /**
     * {@inheritDoc}
     *
     * @return {@code sum(singletons[i] * probabilities[i])}
     */
    public double getNumericalMean() {
        double mean = 0;

        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            mean += sample.getValue() * sample.getKey();
        }

        return mean;
    }

    /**
     * {@inheritDoc}
     *
     * @return {@code sum((singletons[i] - mean) ^ 2 * probabilities[i])}
     */
    public double getNumericalVariance() {
        double mean = 0;
        double meanOfSquares = 0;

        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            mean += sample.getValue() * sample.getKey();
            meanOfSquares += sample.getValue() * sample.getKey() * sample.getKey();
        }

        return meanOfSquares - mean * mean;
    }

    /**
     * {@inheritDoc}
     *
     * Returns the lowest value with non-zero probability.
     *
     * @return the lowest value with non-zero probability.
     */
    public double getSupportLowerBound() {
        double min = Double.POSITIVE_INFINITY;
        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            if (sample.getKey() < min && sample.getValue() > 0) {
                min = sample.getKey();
            }
        }

        return min;
    }

    /**
     * {@inheritDoc}
     *
     * Returns the highest value with non-zero probability.
     *
     * @return the highest value with non-zero probability.
     */
    public double getSupportUpperBound() {
        double max = Double.NEGATIVE_INFINITY;
        for (final Pair<Double, Double> sample : innerDistribution.getPmf()) {
            if (sample.getKey() > max && sample.getValue() > 0) {
                max = sample.getKey();
            }
        }

        return max;
    }

    /**
     * {@inheritDoc}
     *
     * The support of this distribution includes the lower bound.
     *
     * @return {@code true}
     */
    public boolean isSupportLowerBoundInclusive() {
        return true;
    }

    /**
     * {@inheritDoc}
     *
     * The support of this distribution includes the upper bound.
     *
     * @return {@code true}
     */
    public boolean isSupportUpperBoundInclusive() {
        return true;
    }

    /**
     * {@inheritDoc}
     *
     * The support of this distribution is connected.
     *
     * @return {@code true}
     */
    public boolean isSupportConnected() {
        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public double sample() {
        return innerDistribution.sample();
    }
}
