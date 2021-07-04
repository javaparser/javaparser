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
import java.util.List;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.util.Pair;

/**
 * Multivariate normal mixture distribution.
 * This class is mainly syntactic sugar.
 *
 * @see MixtureMultivariateRealDistribution
 * @since 3.2
 */
public class MixtureMultivariateNormalDistribution
    extends MixtureMultivariateRealDistribution<MultivariateNormalDistribution> {

    /**
     * Creates a multivariate normal mixture distribution.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link org.apache.commons.math3.random.Well19937c Well19937c} as random
     * generator to be used for sampling only (see {@link #sample()} and
     * {@link #sample(int)}). In case no sampling is needed for the created
     * distribution, it is advised to pass {@code null} as random generator via
     * the appropriate constructors to avoid the additional initialisation
     * overhead.
     *
     * @param weights Weights of each component.
     * @param means Mean vector for each component.
     * @param covariances Covariance matrix for each component.
     */
    public MixtureMultivariateNormalDistribution(double[] weights,
                                                 double[][] means,
                                                 double[][][] covariances) {
        super(createComponents(weights, means, covariances));
    }

    /**
     * Creates a mixture model from a list of distributions and their
     * associated weights.
     * <p>
     * <b>Note:</b> this constructor will implicitly create an instance of
     * {@link org.apache.commons.math3.random.Well19937c Well19937c} as random
     * generator to be used for sampling only (see {@link #sample()} and
     * {@link #sample(int)}). In case no sampling is needed for the created
     * distribution, it is advised to pass {@code null} as random generator via
     * the appropriate constructors to avoid the additional initialisation
     * overhead.
     *
     * @param components List of (weight, distribution) pairs from which to sample.
     */
    public MixtureMultivariateNormalDistribution(List<Pair<Double, MultivariateNormalDistribution>> components) {
        super(components);
    }

    /**
     * Creates a mixture model from a list of distributions and their
     * associated weights.
     *
     * @param rng Random number generator.
     * @param components Distributions from which to sample.
     * @throws NotPositiveException if any of the weights is negative.
     * @throws DimensionMismatchException if not all components have the same
     * number of variables.
     */
    public MixtureMultivariateNormalDistribution(RandomGenerator rng,
                                                 List<Pair<Double, MultivariateNormalDistribution>> components)
        throws NotPositiveException, DimensionMismatchException {
        super(rng, components);
    }

    /**
     * @param weights Weights of each component.
     * @param means Mean vector for each component.
     * @param covariances Covariance matrix for each component.
     * @return the list of components.
     */
    private static List<Pair<Double, MultivariateNormalDistribution>> createComponents(double[] weights,
                                                                                       double[][] means,
                                                                                       double[][][] covariances) {
        final List<Pair<Double, MultivariateNormalDistribution>> mvns
            = new ArrayList<Pair<Double, MultivariateNormalDistribution>>(weights.length);

        for (int i = 0; i < weights.length; i++) {
            final MultivariateNormalDistribution dist
                = new MultivariateNormalDistribution(means[i], covariances[i]);

            mvns.add(new Pair<Double, MultivariateNormalDistribution>(weights[i], dist));
        }

        return mvns;
    }
}
