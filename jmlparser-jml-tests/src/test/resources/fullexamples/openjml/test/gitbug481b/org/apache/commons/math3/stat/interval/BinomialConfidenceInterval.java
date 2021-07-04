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

import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;

/**
 * Interface to generate confidence intervals for a binomial proportion.
 *
 * @see <a
 *      href="http://en.wikipedia.org/wiki/Binomial_proportion_confidence_interval">Binomial
 *      proportion confidence interval (Wikipedia)</a>
 * @since 3.3
 */
public interface BinomialConfidenceInterval {

    /**
     * Create a confidence interval for the true probability of success
     * of an unknown binomial distribution with the given observed number
     * of trials, successes and confidence level.
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
    ConfidenceInterval createInterval(int numberOfTrials, int numberOfSuccesses, double confidenceLevel)
            throws NotStrictlyPositiveException, NotPositiveException,
                   NumberIsTooLargeException, OutOfRangeException;

}
