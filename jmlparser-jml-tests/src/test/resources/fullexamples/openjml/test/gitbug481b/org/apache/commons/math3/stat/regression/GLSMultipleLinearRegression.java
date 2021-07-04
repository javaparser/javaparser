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

import org.apache.commons.math3.linear.LUDecomposition;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.RealVector;

/**
 * The GLS implementation of multiple linear regression.
 *
 * GLS assumes a general covariance matrix Omega of the error
 * <pre>
 * u ~ N(0, Omega)
 * </pre>
 *
 * Estimated by GLS,
 * <pre>
 * b=(X' Omega^-1 X)^-1X'Omega^-1 y
 * </pre>
 * whose variance is
 * <pre>
 * Var(b)=(X' Omega^-1 X)^-1
 * </pre>
 * @since 2.0
 */
public class GLSMultipleLinearRegression extends AbstractMultipleLinearRegression {

    /** Covariance matrix. */
    private RealMatrix Omega;

    /** Inverse of covariance matrix. */
    private RealMatrix OmegaInverse;

    /** Replace sample data, overriding any previous sample.
     * @param y y values of the sample
     * @param x x values of the sample
     * @param covariance array representing the covariance matrix
     */
    public void newSampleData(double[] y, double[][] x, double[][] covariance) {
        validateSampleData(x, y);
        newYSampleData(y);
        newXSampleData(x);
        validateCovarianceData(x, covariance);
        newCovarianceData(covariance);
    }

    /**
     * Add the covariance data.
     *
     * @param omega the [n,n] array representing the covariance
     */
    protected void newCovarianceData(double[][] omega){
        this.Omega = new Array2DRowRealMatrix(omega);
        this.OmegaInverse = null;
    }

    /**
     * Get the inverse of the covariance.
     * <p>The inverse of the covariance matrix is lazily evaluated and cached.</p>
     * @return inverse of the covariance
     */
    protected RealMatrix getOmegaInverse() {
        if (OmegaInverse == null) {
            OmegaInverse = new LUDecomposition(Omega).getSolver().getInverse();
        }
        return OmegaInverse;
    }

    /**
     * Calculates beta by GLS.
     * <pre>
     *  b=(X' Omega^-1 X)^-1X'Omega^-1 y
     * </pre>
     * @return beta
     */
    @Override
    protected RealVector calculateBeta() {
        RealMatrix OI = getOmegaInverse();
        RealMatrix XT = getX().transpose();
        RealMatrix XTOIX = XT.multiply(OI).multiply(getX());
        RealMatrix inverse = new LUDecomposition(XTOIX).getSolver().getInverse();
        return inverse.multiply(XT).multiply(OI).operate(getY());
    }

    /**
     * Calculates the variance on the beta.
     * <pre>
     *  Var(b)=(X' Omega^-1 X)^-1
     * </pre>
     * @return The beta variance matrix
     */
    @Override
    protected RealMatrix calculateBetaVariance() {
        RealMatrix OI = getOmegaInverse();
        RealMatrix XTOIX = getX().transpose().multiply(OI).multiply(getX());
        return new LUDecomposition(XTOIX).getSolver().getInverse();
    }


    /**
     * Calculates the estimated variance of the error term using the formula
     * <pre>
     *  Var(u) = Tr(u' Omega^-1 u)/(n-k)
     * </pre>
     * where n and k are the row and column dimensions of the design
     * matrix X.
     *
     * @return error variance
     * @since 2.2
     */
    @Override
    protected double calculateErrorVariance() {
        RealVector residuals = calculateResiduals();
        double t = residuals.dotProduct(getOmegaInverse().operate(residuals));
        return t / (getX().getRowDimension() - getX().getColumnDimension());

    }

}
