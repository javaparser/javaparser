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

import org.apache.commons.math3.distribution.FDistribution;

/**
 * Implements the Clopper-Pearson method for creating a binomial proportion confidence interval.
 *
 * @see <a
 *      href="http://en.wikipedia.org/wiki/Binomial_proportion_confidence_interval#Clopper-Pearson_interval">
 *      Clopper-Pearson interval (Wikipedia)</a>
 * @since 3.3
 */
public class ClopperPearsonInterval implements BinomialConfidenceInterval {

    /** {@inheritDoc} */
    public ConfidenceInterval createInterval(int numberOfTrials, int numberOfSuccesses,
                                             double confidenceLevel) {
        IntervalUtils.checkParameters(numberOfTrials, numberOfSuccesses, confidenceLevel);
        double lowerBound = 0;
        double upperBound = 0;
        final double alpha = (1.0 - confidenceLevel) / 2.0;

        final FDistribution distributionLowerBound = new FDistribution(2 * (numberOfTrials - numberOfSuccesses + 1),
                                                                       2 * numberOfSuccesses);
        final double fValueLowerBound = distributionLowerBound.inverseCumulativeProbability(1 - alpha);
        if (numberOfSuccesses > 0) {
            lowerBound = numberOfSuccesses /
                         (numberOfSuccesses + (numberOfTrials - numberOfSuccesses + 1) * fValueLowerBound);
        }

        final FDistribution distributionUpperBound = new FDistribution(2 * (numberOfSuccesses + 1),
                                                                       2 * (numberOfTrials - numberOfSuccesses));
        final double fValueUpperBound = distributionUpperBound.inverseCumulativeProbability(1 - alpha);
        if (numberOfSuccesses > 0) {
            upperBound = (numberOfSuccesses + 1) * fValueUpperBound /
                         (numberOfTrials - numberOfSuccesses + (numberOfSuccesses + 1) * fValueUpperBound);
        }

        return new ConfidenceInterval(lowerBound, upperBound, confidenceLevel);
    }

}
