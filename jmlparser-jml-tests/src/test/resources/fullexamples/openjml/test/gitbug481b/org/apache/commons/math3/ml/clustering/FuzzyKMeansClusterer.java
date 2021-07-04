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
package org.apache.commons.math3.ml.clustering;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.linear.MatrixUtils;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.ml.distance.DistanceMeasure;
import org.apache.commons.math3.ml.distance.EuclideanDistance;
import org.apache.commons.math3.random.JDKRandomGenerator;
import org.apache.commons.math3.random.RandomGenerator;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;

/**
 * Fuzzy K-Means clustering algorithm.
 * <p>
 * The Fuzzy K-Means algorithm is a variation of the classical K-Means algorithm, with the
 * major difference that a single data point is not uniquely assigned to a single cluster.
 * Instead, each point i has a set of weights u<sub>ij</sub> which indicate the degree of membership
 * to the cluster j.
 * <p>
 * The algorithm then tries to minimize the objective function:
 * <pre>
 * J = &#8721;<sub>i=1..C</sub>&#8721;<sub>k=1..N</sub> u<sub>ik</sub><sup>m</sup>d<sub>ik</sub><sup>2</sup>
 * </pre>
 * with d<sub>ik</sub> being the distance between data point i and the cluster center k.
 * <p>
 * The algorithm requires two parameters:
 * <ul>
 *   <li>k: the number of clusters
 *   <li>fuzziness: determines the level of cluster fuzziness, larger values lead to fuzzier clusters
 * </ul>
 * Additional, optional parameters:
 * <ul>
 *   <li>maxIterations: the maximum number of iterations
 *   <li>epsilon: the convergence criteria, default is 1e-3
 * </ul>
 * <p>
 * The fuzzy variant of the K-Means algorithm is more robust with regard to the selection
 * of the initial cluster centers.
 *
 * @param <T> type of the points to cluster
 * @since 3.3
 */
public class FuzzyKMeansClusterer<T extends Clusterable> extends Clusterer<T> {

    /** The default value for the convergence criteria. */
    private static final double DEFAULT_EPSILON = 1e-3;

    /** The number of clusters. */
    private final int k;

    /** The maximum number of iterations. */
    private final int maxIterations;

    /** The fuzziness factor. */
    private final double fuzziness;

    /** The convergence criteria. */
    private final double epsilon;

    /** Random generator for choosing initial centers. */
    private final RandomGenerator random;

    /** The membership matrix. */
    private double[][] membershipMatrix;

    /** The list of points used in the last call to {@link #cluster(Collection)}. */
    private List<T> points;

    /** The list of clusters resulting from the last call to {@link #cluster(Collection)}. */
    private List<CentroidCluster<T>> clusters;

    /**
     * Creates a new instance of a FuzzyKMeansClusterer.
     * <p>
     * The euclidean distance will be used as default distance measure.
     *
     * @param k the number of clusters to split the data into
     * @param fuzziness the fuzziness factor, must be &gt; 1.0
     * @throws NumberIsTooSmallException if {@code fuzziness <= 1.0}
     */
    public FuzzyKMeansClusterer(final int k, final double fuzziness) throws NumberIsTooSmallException {
        this(k, fuzziness, -1, new EuclideanDistance());
    }

    /**
     * Creates a new instance of a FuzzyKMeansClusterer.
     *
     * @param k the number of clusters to split the data into
     * @param fuzziness the fuzziness factor, must be &gt; 1.0
     * @param maxIterations the maximum number of iterations to run the algorithm for.
     *   If negative, no maximum will be used.
     * @param measure the distance measure to use
     * @throws NumberIsTooSmallException if {@code fuzziness <= 1.0}
     */
    public FuzzyKMeansClusterer(final int k, final double fuzziness,
                                final int maxIterations, final DistanceMeasure measure)
            throws NumberIsTooSmallException {
        this(k, fuzziness, maxIterations, measure, DEFAULT_EPSILON, new JDKRandomGenerator());
    }

    /**
     * Creates a new instance of a FuzzyKMeansClusterer.
     *
     * @param k the number of clusters to split the data into
     * @param fuzziness the fuzziness factor, must be &gt; 1.0
     * @param maxIterations the maximum number of iterations to run the algorithm for.
     *   If negative, no maximum will be used.
     * @param measure the distance measure to use
     * @param epsilon the convergence criteria (default is 1e-3)
     * @param random random generator to use for choosing initial centers
     * @throws NumberIsTooSmallException if {@code fuzziness <= 1.0}
     */
    public FuzzyKMeansClusterer(final int k, final double fuzziness,
                                final int maxIterations, final DistanceMeasure measure,
                                final double epsilon, final RandomGenerator random)
            throws NumberIsTooSmallException {

        super(measure);

        if (fuzziness <= 1.0d) {
            throw new NumberIsTooSmallException(fuzziness, 1.0, false);
        }
        this.k = k;
        this.fuzziness = fuzziness;
        this.maxIterations = maxIterations;
        this.epsilon = epsilon;
        this.random = random;

        this.membershipMatrix = null;
        this.points = null;
        this.clusters = null;
    }

    /**
     * Return the number of clusters this instance will use.
     * @return the number of clusters
     */
    public int getK() {
        return k;
    }

    /**
     * Returns the fuzziness factor used by this instance.
     * @return the fuzziness factor
     */
    public double getFuzziness() {
        return fuzziness;
    }

    /**
     * Returns the maximum number of iterations this instance will use.
     * @return the maximum number of iterations, or -1 if no maximum is set
     */
    public int getMaxIterations() {
        return maxIterations;
    }

    /**
     * Returns the convergence criteria used by this instance.
     * @return the convergence criteria
     */
    public double getEpsilon() {
        return epsilon;
    }

    /**
     * Returns the random generator this instance will use.
     * @return the random generator
     */
    public RandomGenerator getRandomGenerator() {
        return random;
    }

    /**
     * Returns the {@code nxk} membership matrix, where {@code n} is the number
     * of data points and {@code k} the number of clusters.
     * <p>
     * The element U<sub>i,j</sub> represents the membership value for data point {@code i}
     * to cluster {@code j}.
     *
     * @return the membership matrix
     * @throws MathIllegalStateException if {@link #cluster(Collection)} has not been called before
     */
    public RealMatrix getMembershipMatrix() {
        if (membershipMatrix == null) {
            throw new MathIllegalStateException();
        }
        return MatrixUtils.createRealMatrix(membershipMatrix);
    }

    /**
     * Returns an unmodifiable list of the data points used in the last
     * call to {@link #cluster(Collection)}.
     * @return the list of data points, or {@code null} if {@link #cluster(Collection)} has
     *   not been called before.
     */
    public List<T> getDataPoints() {
        return points;
    }

    /**
     * Returns the list of clusters resulting from the last call to {@link #cluster(Collection)}.
     * @return the list of clusters, or {@code null} if {@link #cluster(Collection)} has
     *   not been called before.
     */
    public List<CentroidCluster<T>> getClusters() {
        return clusters;
    }

    /**
     * Get the value of the objective function.
     * @return the objective function evaluation as double value
     * @throws MathIllegalStateException if {@link #cluster(Collection)} has not been called before
     */
    public double getObjectiveFunctionValue() {
        if (points == null || clusters == null) {
            throw new MathIllegalStateException();
        }

        int i = 0;
        double objFunction = 0.0;
        for (final T point : points) {
            int j = 0;
            for (final CentroidCluster<T> cluster : clusters) {
                final double dist = distance(point, cluster.getCenter());
                objFunction += (dist * dist) * FastMath.pow(membershipMatrix[i][j], fuzziness);
                j++;
            }
            i++;
        }
        return objFunction;
    }

    /**
     * Performs Fuzzy K-Means cluster analysis.
     *
     * @param dataPoints the points to cluster
     * @return the list of clusters
     * @throws MathIllegalArgumentException if the data points are null or the number
     *     of clusters is larger than the number of data points
     */
    @Override
    public List<CentroidCluster<T>> cluster(final Collection<T> dataPoints)
            throws MathIllegalArgumentException {

        // sanity checks
        MathUtils.checkNotNull(dataPoints);

        final int size = dataPoints.size();

        // number of clusters has to be smaller or equal the number of data points
        if (size < k) {
            throw new NumberIsTooSmallException(size, k, false);
        }

        // copy the input collection to an unmodifiable list with indexed access
        points = Collections.unmodifiableList(new ArrayList<T>(dataPoints));
        clusters = new ArrayList<CentroidCluster<T>>();
        membershipMatrix = new double[size][k];
        final double[][] oldMatrix = new double[size][k];

        // if no points are provided, return an empty list of clusters
        if (size == 0) {
            return clusters;
        }

        initializeMembershipMatrix();

        // there is at least one point
        final int pointDimension = points.get(0).getPoint().length;
        for (int i = 0; i < k; i++) {
            clusters.add(new CentroidCluster<T>(new DoublePoint(new double[pointDimension])));
        }

        int iteration = 0;
        final int max = (maxIterations < 0) ? Integer.MAX_VALUE : maxIterations;
        double difference = 0.0;

        do {
            saveMembershipMatrix(oldMatrix);
            updateClusterCenters();
            updateMembershipMatrix();
            difference = calculateMaxMembershipChange(oldMatrix);
        } while (difference > epsilon && ++iteration < max);

        return clusters;
    }

    /**
     * Update the cluster centers.
     */
    private void updateClusterCenters() {
        int j = 0;
        final List<CentroidCluster<T>> newClusters = new ArrayList<CentroidCluster<T>>(k);
        for (final CentroidCluster<T> cluster : clusters) {
            final Clusterable center = cluster.getCenter();
            int i = 0;
            double[] arr = new double[center.getPoint().length];
            double sum = 0.0;
            for (final T point : points) {
                final double u = FastMath.pow(membershipMatrix[i][j], fuzziness);
                final double[] pointArr = point.getPoint();
                for (int idx = 0; idx < arr.length; idx++) {
                    arr[idx] += u * pointArr[idx];
                }
                sum += u;
                i++;
            }
            MathArrays.scaleInPlace(1.0 / sum, arr);
            newClusters.add(new CentroidCluster<T>(new DoublePoint(arr)));
            j++;
        }
        clusters.clear();
        clusters = newClusters;
    }

    /**
     * Updates the membership matrix and assigns the points to the cluster with
     * the highest membership.
     */
    private void updateMembershipMatrix() {
        for (int i = 0; i < points.size(); i++) {
            final T point = points.get(i);
            double maxMembership = Double.MIN_VALUE;
            int newCluster = -1;
            for (int j = 0; j < clusters.size(); j++) {
                double sum = 0.0;
                final double distA = FastMath.abs(distance(point, clusters.get(j).getCenter()));

                if (distA != 0.0) {
                    for (final CentroidCluster<T> c : clusters) {
                        final double distB = FastMath.abs(distance(point, c.getCenter()));
                        if (distB == 0.0) {
                            sum = Double.POSITIVE_INFINITY;
                            break;
                        }
                        sum += FastMath.pow(distA / distB, 2.0 / (fuzziness - 1.0));
                    }
                }

                double membership;
                if (sum == 0.0) {
                    membership = 1.0;
                } else if (sum == Double.POSITIVE_INFINITY) {
                    membership = 0.0;
                } else {
                    membership = 1.0 / sum;
                }
                membershipMatrix[i][j] = membership;

                if (membershipMatrix[i][j] > maxMembership) {
                    maxMembership = membershipMatrix[i][j];
                    newCluster = j;
                }
            }
            clusters.get(newCluster).addPoint(point);
        }
    }

    /**
     * Initialize the membership matrix with random values.
     */
    private void initializeMembershipMatrix() {
        for (int i = 0; i < points.size(); i++) {
            for (int j = 0; j < k; j++) {
                membershipMatrix[i][j] = random.nextDouble();
            }
            membershipMatrix[i] = MathArrays.normalizeArray(membershipMatrix[i], 1.0);
        }
    }

    /**
     * Calculate the maximum element-by-element change of the membership matrix
     * for the current iteration.
     *
     * @param matrix the membership matrix of the previous iteration
     * @return the maximum membership matrix change
     */
    private double calculateMaxMembershipChange(final double[][] matrix) {
        double maxMembership = 0.0;
        for (int i = 0; i < points.size(); i++) {
            for (int j = 0; j < clusters.size(); j++) {
                double v = FastMath.abs(membershipMatrix[i][j] - matrix[i][j]);
                maxMembership = FastMath.max(v, maxMembership);
            }
        }
        return maxMembership;
    }

    /**
     * Copy the membership matrix into the provided matrix.
     *
     * @param matrix the place to store the membership matrix
     */
    private void saveMembershipMatrix(final double[][] matrix) {
        for (int i = 0; i < points.size(); i++) {
            System.arraycopy(membershipMatrix[i], 0, matrix[i], 0, clusters.size());
        }
    }

}
