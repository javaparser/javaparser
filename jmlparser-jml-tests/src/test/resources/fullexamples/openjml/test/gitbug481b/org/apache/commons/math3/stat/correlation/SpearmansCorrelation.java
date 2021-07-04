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

package org.apache.commons.math3.stat.correlation;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.linear.BlockRealMatrix;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.stat.ranking.NaNStrategy;
import org.apache.commons.math3.stat.ranking.NaturalRanking;
import org.apache.commons.math3.stat.ranking.RankingAlgorithm;

/**
 * Spearman's rank correlation. This implementation performs a rank
 * transformation on the input data and then computes {@link PearsonsCorrelation}
 * on the ranked data.
 * <p>
 * By default, ranks are computed using {@link NaturalRanking} with default
 * strategies for handling NaNs and ties in the data (NaNs maximal, ties averaged).
 * The ranking algorithm can be set using a constructor argument.
 *
 * @since 2.0
 */
public class SpearmansCorrelation {

    /** Input data */
    private final RealMatrix data;

    /** Ranking algorithm  */
    private final RankingAlgorithm rankingAlgorithm;

    /** Rank correlation */
    private final PearsonsCorrelation rankCorrelation;

    /**
     * Create a SpearmansCorrelation without data.
     */
    public SpearmansCorrelation() {
        this(new NaturalRanking());
    }

    /**
     * Create a SpearmansCorrelation with the given ranking algorithm.
     * <p>
     * From version 4.0 onwards this constructor will throw an exception
     * if the provided {@link NaturalRanking} uses a {@link NaNStrategy#REMOVED} strategy.
     *
     * @param rankingAlgorithm ranking algorithm
     * @since 3.1
     */
    public SpearmansCorrelation(final RankingAlgorithm rankingAlgorithm) {
        data = null;
        this.rankingAlgorithm = rankingAlgorithm;
        rankCorrelation = null;
    }

    /**
     * Create a SpearmansCorrelation from the given data matrix.
     *
     * @param dataMatrix matrix of data with columns representing
     * variables to correlate
     */
    public SpearmansCorrelation(final RealMatrix dataMatrix) {
        this(dataMatrix, new NaturalRanking());
    }

    /**
     * Create a SpearmansCorrelation with the given input data matrix
     * and ranking algorithm.
     * <p>
     * From version 4.0 onwards this constructor will throw an exception
     * if the provided {@link NaturalRanking} uses a {@link NaNStrategy#REMOVED} strategy.
     *
     * @param dataMatrix matrix of data with columns representing
     * variables to correlate
     * @param rankingAlgorithm ranking algorithm
     */
    public SpearmansCorrelation(final RealMatrix dataMatrix, final RankingAlgorithm rankingAlgorithm) {
        this.rankingAlgorithm = rankingAlgorithm;
        this.data = rankTransform(dataMatrix);
        rankCorrelation = new PearsonsCorrelation(data);
    }

    /**
     * Calculate the Spearman Rank Correlation Matrix.
     *
     * @return Spearman Rank Correlation Matrix
     * @throws NullPointerException if this instance was created with no data
     */
    public RealMatrix getCorrelationMatrix() {
        return rankCorrelation.getCorrelationMatrix();
    }

    /**
     * Returns a {@link PearsonsCorrelation} instance constructed from the
     * ranked input data. That is,
     * <code>new SpearmansCorrelation(matrix).getRankCorrelation()</code>
     * is equivalent to
     * <code>new PearsonsCorrelation(rankTransform(matrix))</code> where
     * <code>rankTransform(matrix)</code> is the result of applying the
     * configured <code>RankingAlgorithm</code> to each of the columns of
     * <code>matrix.</code>
     *
     * <p>Returns null if this instance was created with no data.</p>
     *
     * @return PearsonsCorrelation among ranked column data
     */
    public PearsonsCorrelation getRankCorrelation() {
        return rankCorrelation;
    }

    /**
     * Computes the Spearman's rank correlation matrix for the columns of the
     * input matrix.
     *
     * @param matrix matrix with columns representing variables to correlate
     * @return correlation matrix
     */
    public RealMatrix computeCorrelationMatrix(final RealMatrix matrix) {
        final RealMatrix matrixCopy = rankTransform(matrix);
        return new PearsonsCorrelation().computeCorrelationMatrix(matrixCopy);
    }

    /**
     * Computes the Spearman's rank correlation matrix for the columns of the
     * input rectangular array.  The columns of the array represent values
     * of variables to be correlated.
     *
     * @param matrix matrix with columns representing variables to correlate
     * @return correlation matrix
     */
    public RealMatrix computeCorrelationMatrix(final double[][] matrix) {
       return computeCorrelationMatrix(new BlockRealMatrix(matrix));
    }

    /**
     * Computes the Spearman's rank correlation coefficient between the two arrays.
     *
     * @param xArray first data array
     * @param yArray second data array
     * @return Returns Spearman's rank correlation coefficient for the two arrays
     * @throws DimensionMismatchException if the arrays lengths do not match
     * @throws MathIllegalArgumentException if the array length is less than 2
     */
    public double correlation(final double[] xArray, final double[] yArray) {
        if (xArray.length != yArray.length) {
            throw new DimensionMismatchException(xArray.length, yArray.length);
        } else if (xArray.length < 2) {
            throw new MathIllegalArgumentException(LocalizedFormats.INSUFFICIENT_DIMENSION,
                                                   xArray.length, 2);
        } else {
            double[] x = xArray;
            double[] y = yArray;
            if (rankingAlgorithm instanceof NaturalRanking &&
                NaNStrategy.REMOVED == ((NaturalRanking) rankingAlgorithm).getNanStrategy()) {
                final Set<Integer> nanPositions = new HashSet<Integer>();

                nanPositions.addAll(getNaNPositions(xArray));
                nanPositions.addAll(getNaNPositions(yArray));

                x = removeValues(xArray, nanPositions);
                y = removeValues(yArray, nanPositions);
            }
            return new PearsonsCorrelation().correlation(rankingAlgorithm.rank(x), rankingAlgorithm.rank(y));
        }
    }

    /**
     * Applies rank transform to each of the columns of <code>matrix</code>
     * using the current <code>rankingAlgorithm</code>.
     *
     * @param matrix matrix to transform
     * @return a rank-transformed matrix
     */
    private RealMatrix rankTransform(final RealMatrix matrix) {
        RealMatrix transformed = null;

        if (rankingAlgorithm instanceof NaturalRanking &&
                ((NaturalRanking) rankingAlgorithm).getNanStrategy() == NaNStrategy.REMOVED) {
            final Set<Integer> nanPositions = new HashSet<Integer>();
            for (int i = 0; i < matrix.getColumnDimension(); i++) {
                nanPositions.addAll(getNaNPositions(matrix.getColumn(i)));
            }

            // if we have found NaN values, we have to update the matrix size
            if (!nanPositions.isEmpty()) {
                transformed = new BlockRealMatrix(matrix.getRowDimension() - nanPositions.size(),
                                                  matrix.getColumnDimension());
                for (int i = 0; i < transformed.getColumnDimension(); i++) {
                    transformed.setColumn(i, removeValues(matrix.getColumn(i), nanPositions));
                }
            }
        }

        if (transformed == null) {
            transformed = matrix.copy();
        }

        for (int i = 0; i < transformed.getColumnDimension(); i++) {
            transformed.setColumn(i, rankingAlgorithm.rank(transformed.getColumn(i)));
        }

        return transformed;
    }

    /**
     * Returns a list containing the indices of NaN values in the input array.
     *
     * @param input the input array
     * @return a list of NaN positions in the input array
     */
    private List<Integer> getNaNPositions(final double[] input) {
        final List<Integer> positions = new ArrayList<Integer>();
        for (int i = 0; i < input.length; i++) {
            if (Double.isNaN(input[i])) {
                positions.add(i);
            }
        }
        return positions;
    }

    /**
     * Removes all values from the input array at the specified indices.
     *
     * @param input the input array
     * @param indices a set containing the indices to be removed
     * @return the input array without the values at the specified indices
     */
    private double[] removeValues(final double[] input, final Set<Integer> indices) {
        if (indices.isEmpty()) {
            return input;
        }
        final double[] result = new double[input.length - indices.size()];
        for (int i = 0, j = 0; i < input.length; i++) {
            if (!indices.contains(i)) {
                result[j++] = input[i];
            }
        }
        return result;
    }
}
