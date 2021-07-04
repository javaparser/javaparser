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
package org.apache.commons.math3.distribution.fitting;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.math3.distribution.MultivariateNormalDistribution;
import org.apache.commons.math3.distribution.MixtureMultivariateNormalDistribution;
import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.NumberIsTooLargeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.SingularMatrixException;
import org.apache.commons.math3.stat.correlation.Covariance;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.Pair;

/**
 * Expectation-Maximization</a> algorithm for fitting the parameters of
 * multivariate normal mixture model distributions.
 *
 * This implementation is pure original code based on <a
 * href="https://www.ee.washington.edu/techsite/papers/documents/UWEETR-2010-0002.pdf">
 * EM Demystified: An Expectation-Maximization Tutorial</a> by Yihua Chen and Maya R. Gupta,
 * Department of Electrical Engineering, University of Washington, Seattle, WA 98195.
 * It was verified using external tools like <a
 * href="http://cran.r-project.org/web/packages/mixtools/index.html">CRAN Mixtools</a>
 * (see the JUnit test cases) but it is <strong>not</strong> based on Mixtools code at all.
 * The discussion of the origin of this class can be seen in the comments of the <a
 * href="https://issues.apache.org/jira/browse/MATH-817">MATH-817</a> JIRA issue.
 * @since 3.2
 */
public class MultivariateNormalMixtureExpectationMaximization {
    /**
     * Default maximum number of iterations allowed per fitting process.
     */
    private static final int DEFAULT_MAX_ITERATIONS = 1000;
    /**
     * Default convergence threshold for fitting.
     */
    private static final double DEFAULT_THRESHOLD = 1E-5;
    /**
     * The data to fit.
     */
    private final double[][] data;
    /**
     * The model fit against the data.
     */
    private MixtureMultivariateNormalDistribution fittedModel;
    /**
     * The log likelihood of the data given the fitted model.
     */
    private double logLikelihood = 0d;

    /**
     * Creates an object to fit a multivariate normal mixture model to data.
     *
     * @param data Data to use in fitting procedure
     * @throws NotStrictlyPositiveException if data has no rows
     * @throws DimensionMismatchException if rows of data have different numbers
     *             of columns
     * @throws NumberIsTooSmallException if the number of columns in the data is
     *             less than 2
     */
    public MultivariateNormalMixtureExpectationMaximization(double[][] data)
        throws NotStrictlyPositiveException,
               DimensionMismatchException,
               NumberIsTooSmallException {
        if (data.length < 1) {
            throw new NotStrictlyPositiveException(data.length);
        }

        this.data = new double[data.length][data[0].length];

        for (int i = 0; i < data.length; i++) {
            if (data[i].length != data[0].length) {
                // Jagged arrays not allowed
                throw new DimensionMismatchException(data[i].length,
                                                     data[0].length);
            }
            if (data[i].length < 2) {
                throw new NumberIsTooSmallException(LocalizedFormats.NUMBER_TOO_SMALL,
                                                    data[i].length, 2, true);
            }
            this.data[i] = MathArrays.copyOf(data[i], data[i].length);
        }
    }

    /**
     * Fit a mixture model to the data supplied to the constructor.
     *
     * The quality of the fit depends on the concavity of the data provided to
     * the constructor and the initial mixture provided to this function. If the
     * data has many local optima, multiple runs of the fitting function with
     * different initial mixtures may be required to find the optimal solution.
     * If a SingularMatrixException is encountered, it is possible that another
     * initialization would work.
     *
     * @param initialMixture Model containing initial values of weights and
     *            multivariate normals
     * @param maxIterations Maximum iterations allowed for fit
     * @param threshold Convergence threshold computed as difference in
     *             logLikelihoods between successive iterations
     * @throws SingularMatrixException if any component's covariance matrix is
     *             singular during fitting
     * @throws NotStrictlyPositiveException if numComponents is less than one
     *             or threshold is less than Double.MIN_VALUE
     * @throws DimensionMismatchException if initialMixture mean vector and data
     *             number of columns are not equal
     */
    public void fit(final MixtureMultivariateNormalDistribution initialMixture,
                    final int maxIterations,
                    final double threshold)
            throws SingularMatrixException,
                   NotStrictlyPositiveException,
                   DimensionMismatchException {
        if (maxIterations < 1) {
            throw new NotStrictlyPositiveException(maxIterations);
        }

        if (threshold < Double.MIN_VALUE) {
            throw new NotStrictlyPositiveException(threshold);
        }

        final int n = data.length;

        // Number of data columns. Jagged data already rejected in constructor,
        // so we can assume the lengths of each row are equal.
        final int numCols = data[0].length;
        final int k = initialMixture.getComponents().size();

        final int numMeanColumns
            = initialMixture.getComponents().get(0).getSecond().getMeans().length;

        if (numMeanColumns != numCols) {
            throw new DimensionMismatchException(numMeanColumns, numCols);
        }

        int numIterations = 0;
        double previousLogLikelihood = 0d;

        logLikelihood = Double.NEGATIVE_INFINITY;

        // Initialize model to fit to initial mixture.
        fittedModel = new MixtureMultivariateNormalDistribution(initialMixture.getComponents());

        while (numIterations++ <= maxIterations &&
               FastMath.abs(previousLogLikelihood - logLikelihood) > threshold) {
            previousLogLikelihood = logLikelihood;
            double sumLogLikelihood = 0d;

            // Mixture components
            final List<Pair<Double, MultivariateNormalDistribution>> components
                = fittedModel.getComponents();

            // Weight and distribution of each component
            final double[] weights = new double[k];

            final MultivariateNormalDistribution[] mvns = new MultivariateNormalDistribution[k];

            for (int j = 0; j < k; j++) {
                weights[j] = components.get(j).getFirst();
                mvns[j] = components.get(j).getSecond();
            }

            // E-step: compute the data dependent parameters of the expectation
            // function.
            // The percentage of row's total density between a row and a
            // component
            final double[][] gamma = new double[n][k];

            // Sum of gamma for each component
            final double[] gammaSums = new double[k];

            // Sum of gamma times its row for each each component
            final double[][] gammaDataProdSums = new double[k][numCols];

            for (int i = 0; i < n; i++) {
                final double rowDensity = fittedModel.density(data[i]);
                sumLogLikelihood += FastMath.log(rowDensity);

                for (int j = 0; j < k; j++) {
                    gamma[i][j] = weights[j] * mvns[j].density(data[i]) / rowDensity;
                    gammaSums[j] += gamma[i][j];

                    for (int col = 0; col < numCols; col++) {
                        gammaDataProdSums[j][col] += gamma[i][j] * data[i][col];
                    }
                }
            }

            logLikelihood = sumLogLikelihood / n;

            // M-step: compute the new parameters based on the expectation
            // function.
            final double[] newWeights = new double[k];
            final double[][] newMeans = new double[k][numCols];

            for (int j = 0; j < k; j++) {
                newWeights[j] = gammaSums[j] / n;
                for (int col = 0; col < numCols; col++) {
                    newMeans[j][col] = gammaDataProdSums[j][col] / gammaSums[j];
                }
            }

            // Compute new covariance matrices
            final RealMatrix[] newCovMats = new RealMatrix[k];
            for (int j = 0; j < k; j++) {
                newCovMats[j] = new Array2DRowRealMatrix(numCols, numCols);
            }
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < k; j++) {
                    final RealMatrix vec
                        = new Array2DRowRealMatrix(MathArrays.ebeSubtract(data[i], newMeans[j]));
                    final RealMatrix dataCov
                        = vec.multiply(vec.transpose()).scalarMultiply(gamma[i][j]);
                    newCovMats[j] = newCovMats[j].add(dataCov);
                }
            }

            // Converting to arrays for use by fitted model
            final double[][][] newCovMatArrays = new double[k][numCols][numCols];
            for (int j = 0; j < k; j++) {
                newCovMats[j] = newCovMats[j].scalarMultiply(1d / gammaSums[j]);
                newCovMatArrays[j] = newCovMats[j].getData();
            }

            // Update current model
            fittedModel = new MixtureMultivariateNormalDistribution(newWeights,
                                                                    newMeans,
                                                                    newCovMatArrays);
        }

        if (FastMath.abs(previousLogLikelihood - logLikelihood) > threshold) {
            // Did not converge before the maximum number of iterations
            throw new ConvergenceException();
        }
    }

    /**
     * Fit a mixture model to the data supplied to the constructor.
     *
     * The quality of the fit depends on the concavity of the data provided to
     * the constructor and the initial mixture provided to this function. If the
     * data has many local optima, multiple runs of the fitting function with
     * different initial mixtures may be required to find the optimal solution.
     * If a SingularMatrixException is encountered, it is possible that another
     * initialization would work.
     *
     * @param initialMixture Model containing initial values of weights and
     *            multivariate normals
     * @throws SingularMatrixException if any component's covariance matrix is
     *             singular during fitting
     * @throws NotStrictlyPositiveException if numComponents is less than one or
     *             threshold is less than Double.MIN_VALUE
     */
    public void fit(MixtureMultivariateNormalDistribution initialMixture)
        throws SingularMatrixException,
               NotStrictlyPositiveException {
        fit(initialMixture, DEFAULT_MAX_ITERATIONS, DEFAULT_THRESHOLD);
    }

    /**
     * Helper method to create a multivariate normal mixture model which can be
     * used to initialize {@link #fit(MixtureMultivariateNormalDistribution)}.
     *
     * This method uses the data supplied to the constructor to try to determine
     * a good mixture model at which to start the fit, but it is not guaranteed
     * to supply a model which will find the optimal solution or even converge.
     *
     * @param data Data to estimate distribution
     * @param numComponents Number of components for estimated mixture
     * @return Multivariate normal mixture model estimated from the data
     * @throws NumberIsTooLargeException if {@code numComponents} is greater
     * than the number of data rows.
     * @throws NumberIsTooSmallException if {@code numComponents < 2}.
     * @throws NotStrictlyPositiveException if data has less than 2 rows
     * @throws DimensionMismatchException if rows of data have different numbers
     *             of columns
     */
    public static MixtureMultivariateNormalDistribution estimate(final double[][] data,
                                                                 final int numComponents)
        throws NotStrictlyPositiveException,
               DimensionMismatchException {
        if (data.length < 2) {
            throw new NotStrictlyPositiveException(data.length);
        }
        if (numComponents < 2) {
            throw new NumberIsTooSmallException(numComponents, 2, true);
        }
        if (numComponents > data.length) {
            throw new NumberIsTooLargeException(numComponents, data.length, true);
        }

        final int numRows = data.length;
        final int numCols = data[0].length;

        // sort the data
        final DataRow[] sortedData = new DataRow[numRows];
        for (int i = 0; i < numRows; i++) {
            sortedData[i] = new DataRow(data[i]);
        }
        Arrays.sort(sortedData);

        // uniform weight for each bin
        final double weight = 1d / numComponents;

        // components of mixture model to be created
        final List<Pair<Double, MultivariateNormalDistribution>> components =
                new ArrayList<Pair<Double, MultivariateNormalDistribution>>(numComponents);

        // create a component based on data in each bin
        for (int binIndex = 0; binIndex < numComponents; binIndex++) {
            // minimum index (inclusive) from sorted data for this bin
            final int minIndex = (binIndex * numRows) / numComponents;

            // maximum index (exclusive) from sorted data for this bin
            final int maxIndex = ((binIndex + 1) * numRows) / numComponents;

            // number of data records that will be in this bin
            final int numBinRows = maxIndex - minIndex;

            // data for this bin
            final double[][] binData = new double[numBinRows][numCols];

            // mean of each column for the data in the this bin
            final double[] columnMeans = new double[numCols];

            // populate bin and create component
            for (int i = minIndex, iBin = 0; i < maxIndex; i++, iBin++) {
                for (int j = 0; j < numCols; j++) {
                    final double val = sortedData[i].getRow()[j];
                    columnMeans[j] += val;
                    binData[iBin][j] = val;
                }
            }

            MathArrays.scaleInPlace(1d / numBinRows, columnMeans);

            // covariance matrix for this bin
            final double[][] covMat
                = new Covariance(binData).getCovarianceMatrix().getData();
            final MultivariateNormalDistribution mvn
                = new MultivariateNormalDistribution(columnMeans, covMat);

            components.add(new Pair<Double, MultivariateNormalDistribution>(weight, mvn));
        }

        return new MixtureMultivariateNormalDistribution(components);
    }

    /**
     * Gets the log likelihood of the data under the fitted model.
     *
     * @return Log likelihood of data or zero of no data has been fit
     */
    public double getLogLikelihood() {
        return logLikelihood;
    }

    /**
     * Gets the fitted model.
     *
     * @return fitted model or {@code null} if no fit has been performed yet.
     */
    public MixtureMultivariateNormalDistribution getFittedModel() {
        return new MixtureMultivariateNormalDistribution(fittedModel.getComponents());
    }

    /**
     * Class used for sorting user-supplied data.
     */
    private static class DataRow implements Comparable<DataRow> {
        /** One data row. */
        private final double[] row;
        /** Mean of the data row. */
        private Double mean;

        /**
         * Create a data row.
         * @param data Data to use for the row
         */
        DataRow(final double[] data) {
            // Store reference.
            row = data;
            // Compute mean.
            mean = 0d;
            for (int i = 0; i < data.length; i++) {
                mean += data[i];
            }
            mean /= data.length;
        }

        /**
         * Compare two data rows.
         * @param other The other row
         * @return int for sorting
         */
        public int compareTo(final DataRow other) {
            return mean.compareTo(other.mean);
        }

        /** {@inheritDoc} */
        @Override
        public boolean equals(Object other) {

            if (this == other) {
                return true;
            }

            if (other instanceof DataRow) {
                return MathArrays.equals(row, ((DataRow) other).row);
            }

            return false;

        }

        /** {@inheritDoc} */
        @Override
        public int hashCode() {
            return Arrays.hashCode(row);
        }
        /**
         * Get a data row.
         * @return data row array
         */
        public double[] getRow() {
            return row;
        }
    }
}

