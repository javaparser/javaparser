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

/**
 * The multiple linear regression can be represented in matrix-notation.
 * <pre>
 *  y=X*b+u
 * </pre>
 * where y is an <code>n-vector</code> <b>regressand</b>, X is a <code>[n,k]</code> matrix whose <code>k</code> columns are called
 * <b>regressors</b>, b is <code>k-vector</code> of <b>regression parameters</b> and <code>u</code> is an <code>n-vector</code>
 * of <b>error terms</b> or <b>residuals</b>.
 *
 * The notation is quite standard in literature,
 * cf eg <a href="http://www.econ.queensu.ca/ETM">Davidson and MacKinnon, Econometrics Theory and Methods, 2004</a>.
 * @since 2.0
 */
public interface MultipleLinearRegression {

    /**
     * Estimates the regression parameters b.
     *
     * @return The [k,1] array representing b
     */
    double[] estimateRegressionParameters();

    /**
     * Estimates the variance of the regression parameters, ie Var(b).
     *
     * @return The [k,k] array representing the variance of b
     */
    double[][] estimateRegressionParametersVariance();

    /**
     * Estimates the residuals, ie u = y - X*b.
     *
     * @return The [n,1] array representing the residuals
     */
    double[] estimateResiduals();

    /**
     * Returns the variance of the regressand, ie Var(y).
     *
     * @return The double representing the variance of y
     */
    double estimateRegressandVariance();

    /**
     * Returns the standard errors of the regression parameters.
     *
     * @return standard errors of estimated regression parameters
     */
     double[] estimateRegressionParametersStandardErrors();

}
