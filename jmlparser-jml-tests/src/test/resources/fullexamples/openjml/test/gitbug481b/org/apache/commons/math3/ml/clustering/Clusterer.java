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
import org.apache.commons.math3.ml.distance.DistanceMeasure;

/**
 * Base class for clustering algorithms.
 *
 * @param <T> the type of points that can be clustered
 * @since 3.2
 */
public abstract class Clusterer<T extends Clusterable> {

    /** The distance measure to use. */
    private DistanceMeasure measure;

    /**
     * Build a new clusterer with the given {@link DistanceMeasure}.
     *
     * @param measure the distance measure to use
     */
    protected Clusterer(final DistanceMeasure measure) {
        this.measure = measure;
    }

    /**
     * Perform a cluster analysis on the given set of {@link Clusterable} instances.
     *
     * @param points the set of {@link Clusterable} instances
     * @return a {@link List} of clusters
     * @throws MathIllegalArgumentException if points are null or the number of
     *   data points is not compatible with this clusterer
     * @throws ConvergenceException if the algorithm has not yet converged after
     *   the maximum number of iterations has been exceeded
     */
    public abstract List<? extends Cluster<T>> cluster(Collection<T> points)
            throws MathIllegalArgumentException, ConvergenceException;

    /**
     * Returns the {@link DistanceMeasure} instance used by this clusterer.
     *
     * @return the distance measure
     */
    public DistanceMeasure getDistanceMeasure() {
        return measure;
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

}
