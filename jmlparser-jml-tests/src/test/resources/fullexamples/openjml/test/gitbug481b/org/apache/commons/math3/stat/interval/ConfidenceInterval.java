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

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Represents an interval estimate of a population parameter.
 *
 * @since 3.3
 */
public class ConfidenceInterval {

    /** Lower endpoint of the interval */
    private double lowerBound;

    /** Upper endpoint of the interval */
    private double upperBound;

    /**
     * The asserted probability that the interval contains the population
     * parameter
     */
    private double confidenceLevel;

    /**
     * Create a confidence interval with the given bounds and confidence level.
     * <p>
     * Preconditions:
     * <ul>
     * <li>{@code lower} must be strictly less than {@code upper}</li>
     * <li>{@code confidenceLevel} must be strictly between 0 and 1 (exclusive)</li>
     * </ul>
     * </p>
     *
     * @param lowerBound lower endpoint of the interval
     * @param upperBound upper endpoint of the interval
     * @param confidenceLevel coverage probability
     * @throws MathIllegalArgumentException if the preconditions are not met
     */
    public ConfidenceInterval(double lowerBound, double upperBound, double confidenceLevel) {
        checkParameters(lowerBound, upperBound, confidenceLevel);
        this.lowerBound = lowerBound;
        this.upperBound = upperBound;
        this.confidenceLevel = confidenceLevel;
    }

    /**
     * @return the lower endpoint of the interval
     */
    public double getLowerBound() {
        return lowerBound;
    }

    /**
     * @return the upper endpoint of the interval
     */
    public double getUpperBound() {
        return upperBound;
    }

    /**
     * @return the asserted probability that the interval contains the
     *         population parameter
     */
    public double getConfidenceLevel() {
        return confidenceLevel;
    }

    /**
     * @return String representation of the confidence interval
     */
    @Override
    public String toString() {
        return "[" + lowerBound + ";" + upperBound + "] (confidence level:" + confidenceLevel + ")";
    }

    /**
     * Verifies that (lower, upper) is a valid non-empty interval and confidence
     * is strictly between 0 and 1.
     *
     * @param lower lower endpoint
     * @param upper upper endpoint
     * @param confidence confidence level
     */
    private void checkParameters(double lower, double upper, double confidence) {
        if (lower >= upper) {
            throw new MathIllegalArgumentException(LocalizedFormats.LOWER_BOUND_NOT_BELOW_UPPER_BOUND, lower, upper);
        }
        if (confidence <= 0 || confidence >= 1) {
            throw new MathIllegalArgumentException(LocalizedFormats.OUT_OF_BOUNDS_CONFIDENCE_LEVEL, confidence, 0, 1);
        }
    }
}
