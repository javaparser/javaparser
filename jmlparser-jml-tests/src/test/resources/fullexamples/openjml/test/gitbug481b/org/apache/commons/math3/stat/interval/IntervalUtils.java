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
package org.apache.commons.math3.stat.interval;

import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Factory methods to generate confidence intervals for a binomial proportion.
 * The supported methods are:
 * <ul>
 * <li>Agresti-Coull interval</li>
 * <li>Clopper-Pearson method (exact method)</li>
 * <li>Normal approximation (based on central limit theorem)</li>
 * <li>Wilson score interval</li>
 * </ul>
 *
 * @since 3.3
 */
public final class IntervalUtils {

    /** Singleton Agresti-Coull instance. */
    private static final BinomialConfidenceInterval AGRESTI_COULL = new AgrestiCoullInterval();

    /** Singleton Clopper-Pearson instance. */
    private static final BinomialConfidenceInterval CLOPPER_PEARSON = new ClopperPearsonInterval();

    /** Singleton NormalApproximation instance. */
    private static final BinomialConfidenceInterval NORMAL_APPROXIMATION = new NormalApproximationInterval();

    /** Singleton Wilson score instance. */
    private static final BinomialConfidenceInterval WILSON_SCORE = new WilsonScoreInterval();

    /**
     * Prevent instantiation.
     */
    private IntervalUtils() {
    }

    /**
     * Create an Agresti-Coull binomial confidence interval for the true
     * probability of success of an unknown binomial distribution with the given
     * observed number of trials, successes and confidence level.
     *
     * @param numberOfTrials number of trials
     * @param numberOfSuccesses number of successes
     * @param confidenceLevel desired probability that the true probability of
     *        success falls within the returned interval
     * @return Confidence interval containing the probability of success with
     *         probability {@code confidenceLevel}
     * @throws NotStrictlyPositiveException if {@code numberOfTrials <= 0}.
     * @throws NotPositiveException if {@code numberOfSuccesses < 0}.
     * @throws NumberIsTooLargeException if {@code numberOfSuccesses > numberOfTrials}.
     * @throws OutOfRangeException if {@code confidenceLevel} is not in the interval {@code (0, 1)}.
     */
    public static ConfidenceInterval getAgrestiCoullInterval(int numberOfTrials, int numberOfSuccesses,
                                                             double confidenceLevel) {
        return AGRESTI_COULL.createInterval(numberOfTrials, numberOfSuccesses, confidenceLevel);
    }

    /**
     * Create a Clopper-Pearson binomial confidence interval for the true
     * probability of success of an unknown binomial distribution with the given
     * observed number of trials, successes and confidence level.
     * <p>
     * Preconditions:
     * <ul>
     * <li>{@code numberOfTrials} must be positive</li>
     * <li>{@code numberOfSuccesses} may not exceed {@code numberOfTrials}</li>
     * <li>{@code confidenceLevel} must be strictly between 0 and 1 (exclusive)</li>
     * </ul>
     * </p>
     *
     * @param numberOfTrials number of trials
     * @param numberOfSuccesses number of successes
     * @param confidenceLevel desired probability that the true probability of
     *        success falls within the returned interval
     * @return Confidence interval containing the probability of success with
     *         probability {@code confidenceLevel}
     * @throws NotStrictlyPositiveException if {@code numberOfTrials <= 0}.
     * @throws NotPositiveException if {@code numberOfSuccesses < 0}.
     * @throws NumberIsTooLargeException if {@code numberOfSuccesses > numberOfTrials}.
     * @throws OutOfRangeException if {@code confidenceLevel} is not in the interval {@code (0, 1)}.
     */
    public static ConfidenceInterval getClopperPearsonInterval(int numberOfTrials, int numberOfSuccesses,
                                                               double confidenceLevel) {
        return CLOPPER_PEARSON.createInterval(numberOfTrials, numberOfSuccesses, confidenceLevel);
    }

    /**
     * Create a binomial confidence interval for the true probability of success
     * of an unknown binomial distribution with the given observed number of
     * trials, successes and confidence level using the Normal approximation to
     * the binomial distribution.
     *
     * @param numberOfTrials number of trials
     * @param numberOfSuccesses number of successes
     * @param confidenceLevel desired probability that the true probability of
     *        success falls within the interval
     * @return Confidence interval containing the probability of success with
     *         probability {@code confidenceLevel}
     */
    public static ConfidenceInterval getNormalApproximationInterval(int numberOfTrials, int numberOfSuccesses,
                                                                    double confidenceLevel) {
        return NORMAL_APPROXIMATION.createInterval(numberOfTrials, numberOfSuccesses, confidenceLevel);
    }

    /**
     * Create a Wilson score binomial confidence interval for the true
     * probability of success of an unknown binomial distribution with the given
     * observed number of trials, successes and confidence level.
     *
     * @param numberOfTrials number of trials
     * @param numberOfSuccesses number of successes
     * @param confidenceLevel desired probability that the true probability of
     *        success falls within the returned interval
     * @return Confidence interval containing the probability of success with
     *         probability {@code confidenceLevel}
     * @throws NotStrictlyPositiveException if {@code numberOfTrials <= 0}.
     * @throws NotPositiveException if {@code numberOfSuccesses < 0}.
     * @throws NumberIsTooLargeException if {@code numberOfSuccesses > numberOfTrials}.
     * @throws OutOfRangeException if {@code confidenceLevel} is not in the interval {@code (0, 1)}.
     */
    public static ConfidenceInterval getWilsonScoreInterval(int numberOfTrials, int numberOfSuccesses,
                                                            double confidenceLevel) {
        return WILSON_SCORE.createInterval(numberOfTrials, numberOfSuccesses, confidenceLevel);
    }

    /**
     * Verifies that parameters satisfy preconditions.
     *
     * @param numberOfTrials number of trials (must be positive)
     * @param numberOfSuccesses number of successes (must not exceed numberOfTrials)
     * @param confidenceLevel confidence level (must be strictly between 0 and 1)
     * @throws NotStrictlyPositiveException if {@code numberOfTrials <= 0}.
     * @throws NotPositiveException if {@code numberOfSuccesses < 0}.
     * @throws NumberIsTooLargeException if {@code numberOfSuccesses > numberOfTrials}.
     * @throws OutOfRangeException if {@code confidenceLevel} is not in the interval {@code (0, 1)}.
     */
    static void checkParameters(int numberOfTrials, int numberOfSuccesses, double confidenceLevel) {
        if (numberOfTrials <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.NUMBER_OF_TRIALS, numberOfTrials);
        }
        if (numberOfSuccesses < 0) {
            throw new NotPositiveException(LocalizedFormats.NEGATIVE_NUMBER_OF_SUCCESSES, numberOfSuccesses);
        }
        if (numberOfSuccesses > numberOfTrials) {
            throw new NumberIsTooLargeException(LocalizedFormats.NUMBER_OF_SUCCESS_LARGER_THAN_POPULATION_SIZE,
                                                numberOfSuccesses, numberOfTrials, true);
        }
        if (confidenceLevel <= 0 || confidenceLevel >= 1) {
            throw new OutOfRangeException(LocalizedFormats.OUT_OF_BOUNDS_CONFIDENCE_LEVEL,
                                          confidenceLevel, 0, 1);
        }
    }

}
