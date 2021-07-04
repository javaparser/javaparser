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
package org.apache.commons.math3.stat.regression;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NoDataException;

/**
 * An interface for regression models allowing for dynamic updating of the data.
 * That is, the entire data set need not be loaded into memory. As observations
 * become available, they can be added to the regression  model and an updated
 * estimate regression statistics can be calculated.
 *
 * @since 3.0
 */
public interface UpdatingMultipleLinearRegression {

    /**
     * Returns true if a constant has been included false otherwise.
     *
     * @return true if constant exists, false otherwise
     */
    boolean hasIntercept();

    /**
     * Returns the number of observations added to the regression model.
     *
     * @return Number of observations
     */
    long getN();

    /**
     * Adds one observation to the regression model.
     *
     * @param x the independent variables which form the design matrix
     * @param y the dependent or response variable
     * @throws ModelSpecificationException if the length of {@code x} does not equal
     * the number of independent variables in the model
     */
    void addObservation(double[] x, double y) throws ModelSpecificationException;

    /**
     * Adds a series of observations to the regression model. The lengths of
     * x and y must be the same and x must be rectangular.
     *
     * @param x a series of observations on the independent variables
     * @param y a series of observations on the dependent variable
     * The length of x and y must be the same
     * @throws ModelSpecificationException if {@code x} is not rectangular, does not match
     * the length of {@code y} or does not contain sufficient data to estimate the model
     */
    void addObservations(double[][] x, double[] y) throws ModelSpecificationException;

    /**
     * Clears internal buffers and resets the regression model. This means all
     * data and derived values are initialized
     */
    void clear();


    /**
     * Performs a regression on data present in buffers and outputs a RegressionResults object
     * @return RegressionResults acts as a container of regression output
     * @throws ModelSpecificationException if the model is not correctly specified
     * @throws NoDataException if there is not sufficient data in the model to
     * estimate the regression parameters
     */
    RegressionResults regress() throws ModelSpecificationException, NoDataException;

    /**
     * Performs a regression on data present in buffers including only regressors
     * indexed in variablesToInclude and outputs a RegressionResults object
     * @param variablesToInclude an array of indices of regressors to include
     * @return RegressionResults acts as a container of regression output
     * @throws ModelSpecificationException if the model is not correctly specified
     * @throws MathIllegalArgumentException if the variablesToInclude array is null or zero length
     */
    RegressionResults regress(int[] variablesToInclude) throws ModelSpecificationException, MathIllegalArgumentException;
}
