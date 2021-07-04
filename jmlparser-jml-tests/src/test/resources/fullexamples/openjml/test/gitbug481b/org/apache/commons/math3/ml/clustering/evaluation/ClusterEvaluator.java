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

package org.apache.commons.math3.ml.clustering.evaluation;

import java.util.List;

import org.apache.commons.math3.ml.clustering.CentroidCluster;
import org.apache.commons.math3.ml.clustering.Cluster;
import org.apache.commons.math3.ml.clustering.Clusterable;
import org.apache.commons.math3.ml.clustering.DoublePoint;
import org.apache.commons.math3.ml.distance.DistanceMeasure;
import org.apache.commons.math3.ml.distance.EuclideanDistance;

/**
 * Base class for cluster evaluation methods.
 *
 * @param <T> type of the clustered points
 * @since 3.3
 */
public abstract class ClusterEvaluator<T extends Clusterable> {

    /** The distance measure to use when evaluating the cluster. */
    private final DistanceMeasure measure;

    /**
     * Creates a new cluster evaluator with an {@link EuclideanDistance}
     * as distance measure.
     */
    public ClusterEvaluator() {
        this(new EuclideanDistance());
    }

    /**
     * Creates a new cluster evaluator with the given distance measure.
     * @param measure the distance measure to use
     */
    public ClusterEvaluator(final DistanceMeasure measure) {
        this.measure = measure;
    }

    /**
     * Computes the evaluation score for the given list of clusters.
     * @param clusters the clusters to evaluate
     * @return the computed score
     */
    public abstract double score(List<? extends Cluster<T>> clusters);

    /**
     * Returns whether the first evaluation score is considered to be better
     * than the second one by this evaluator.
     * <p>
     * Specific implementations shall override this method if the returned scores
     * do not follow the same ordering, i.e. smaller score is better.
     *
     * @param score1 the first score
     * @param score2 the second score
     * @return {@code true} if the first score is considered to be better, {@code false} otherwise
     */
    public boolean isBetterScore(double score1, double score2) {
        return score1 < score2;
    }

    /**
     * Calculates the distance between two {@link Clusterable} instances
     * with the configured {@link DistanceMeasure}.
     *
     * @param p1 the first clusterable
     * @param p2 the second clusterable
     * @return the distance between the two clusterables
     */
    protected double distance(final Clusterable p1, final Clusterable p2) {
        return measure.compute(p1.getPoint(), p2.getPoint());
    }

    /**
     * Computes the centroid for a cluster.
     *
     * @param cluster the cluster
     * @return the computed centroid for the cluster,
     * or {@code null} if the cluster does not contain any points
     */
    protected Clusterable centroidOf(final Cluster<T> cluster) {
        final List<T> points = cluster.getPoints();
        if (points.isEmpty()) {
            return null;
        }

        // in case the cluster is of type CentroidCluster, no need to compute the centroid
        if (cluster instanceof CentroidCluster) {
            return ((CentroidCluster<T>) cluster).getCenter();
        }

        final int dimension = points.get(0).getPoint().length;
        final double[] centroid = new double[dimension];
        for (final T p : points) {
            final double[] point = p.getPoint();
            for (int i = 0; i < centroid.length; i++) {
                centroid[i] += point[i];
            }
        }
        for (int i = 0; i < centroid.length; i++) {
            centroid[i] /= points.size();
        }
        return new DoublePoint(centroid);
    }

}
