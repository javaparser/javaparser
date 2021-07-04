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
package org.apache.commons.math3.stat.descriptive;

import org.apache.commons.math3.linear.RealMatrix;

/**
 *  Reporting interface for basic multivariate statistics.
 *
 * @since 1.2
 */
public interface StatisticalMultivariateSummary {

    /**
     * Returns the dimension of the data
     * @return The dimension of the data
     */
    int getDimension();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * mean of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component means
     */
    double[] getMean();

    /**
     * Returns the covariance of the available values.
     * @return The covariance, null if no multivariate sample
     * have been added or a zeroed matrix for a single value set.
     */
    RealMatrix getCovariance();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * standard deviation of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component standard deviations
     */
    double[] getStandardDeviation();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * maximum of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component maxima
     */
    double[] getMax();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * minimum of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component minima
     */
    double[] getMin();

    /**
     * Returns the number of available values
     * @return The number of available values
     */
    long getN();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * geometric mean of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component geometric means
     */
    double[] getGeometricMean();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * sum of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component sums
     */
    double[] getSum();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * sum of squares of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component sums of squares
     */
    double[] getSumSq();

    /**
     * Returns an array whose i<sup>th</sup> entry is the
     * sum of logs of the i<sup>th</sup> entries of the arrays
     * that correspond to each multivariate sample
     *
     * @return the array of component log sums
     */
    double[] getSumLog();

}
