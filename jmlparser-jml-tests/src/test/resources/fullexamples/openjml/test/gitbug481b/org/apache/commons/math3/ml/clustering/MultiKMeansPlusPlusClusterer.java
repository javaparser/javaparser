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

import java.util.Collection;
import java.util.List;

import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.ml.clustering.evaluation.ClusterEvaluator;
import org.apache.commons.math3.ml.clustering.evaluation.SumOfClusterVariances;

/**
 * A wrapper around a k-means++ clustering algorithm which performs multiple trials
 * and returns the best solution.
 * @param <T> type of the points to cluster
 * @since 3.2
 */
public class MultiKMeansPlusPlusClusterer<T extends Clusterable> extends Clusterer<T> {

    /** The underlying k-means clusterer. */
    private final KMeansPlusPlusClusterer<T> clusterer;

    /** The number of trial runs. */
    private final int numTrials;

    /** The cluster evaluator to use. */
    private final ClusterEvaluator<T> evaluator;

    /** Build a clusterer.
     * @param clusterer the k-means clusterer to use
     * @param numTrials number of trial runs
     */
    public MultiKMeansPlusPlusClusterer(final KMeansPlusPlusClusterer<T> clusterer,
                                        final int numTrials) {
        this(clusterer, numTrials, new SumOfClusterVariances<T>(clusterer.getDistanceMeasure()));
    }

    /** Build a clusterer.
     * @param clusterer the k-means clusterer to use
     * @param numTrials number of trial runs
     * @param evaluator the cluster evaluator to use
     * @since 3.3
     */
    public MultiKMeansPlusPlusClusterer(final KMeansPlusPlusClusterer<T> clusterer,
                                        final int numTrials,
                                        final ClusterEvaluator<T> evaluator) {
        super(clusterer.getDistanceMeasure());
        this.clusterer = clusterer;
        this.numTrials = numTrials;
        this.evaluator = evaluator;
    }

    /**
     * Returns the embedded k-means clusterer used by this instance.
     * @return the embedded clusterer
     */
    public KMeansPlusPlusClusterer<T> getClusterer() {
        return clusterer;
    }

    /**
     * Returns the number of trials this instance will do.
     * @return the number of trials
     */
    public int getNumTrials() {
        return numTrials;
    }

    /**
     * Returns the {@link ClusterEvaluator} used to determine the "best" clustering.
     * @return the used {@link ClusterEvaluator}
     * @since 3.3
     */
    public ClusterEvaluator<T> getClusterEvaluator() {
       return evaluator;
    }

    /**
     * Runs the K-means++ clustering algorithm.
     *
     * @param points the points to cluster
     * @return a list of clusters containing the points
     * @throws MathIllegalArgumentException if the data points are null or the number
     *   of clusters is larger than the number of data points
     * @throws ConvergenceException if an empty cluster is encountered and the
     *   underlying {@link KMeansPlusPlusClusterer} has its
     *   {@link KMeansPlusPlusClusterer.EmptyClusterStrategy} is set to {@code ERROR}.
     */
    @Override
    public List<CentroidCluster<T>> cluster(final Collection<T> points)
        throws MathIllegalArgumentException, ConvergenceException {

        // at first, we have not found any clusters list yet
        List<CentroidCluster<T>> best = null;
        double bestVarianceSum = Double.POSITIVE_INFINITY;

        // do several clustering trials
        for (int i = 0; i < numTrials; ++i) {

            // compute a clusters list
            List<CentroidCluster<T>> clusters = clusterer.cluster(points);

            // compute the variance of the current list
            final double varianceSum = evaluator.score(clusters);

            if (evaluator.isBetterScore(varianceSum, bestVarianceSum)) {
                // this one is the best we have found so far, remember it
                best            = clusters;
                bestVarianceSum = varianceSum;
            }

        }

        // return the best clusters list found
        return best;

    }

}
