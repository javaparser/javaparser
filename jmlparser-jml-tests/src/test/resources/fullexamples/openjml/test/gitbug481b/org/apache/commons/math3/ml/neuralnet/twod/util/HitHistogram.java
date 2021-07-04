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

package org.apache.commons.math3.ml.neuralnet.twod.util;

import org.apache.commons.math3.ml.neuralnet.MapUtils;
import org.apache.commons.math3.ml.neuralnet.Neuron;
import org.apache.commons.math3.ml.neuralnet.twod.NeuronSquareMesh2D;
import org.apache.commons.math3.ml.distance.DistanceMeasure;

/**
 * Computes the hit histogram.
 * Each bin will contain the number of data for which the corresponding
 * neuron is the best matching unit.
 * @since 3.6
 */
public class HitHistogram implements MapDataVisualization {
    /** Distance. */
    private final DistanceMeasure distance;
    /** Whether to compute relative bin counts. */
    private final boolean normalizeCount;

    /**
     * @param normalizeCount Whether to compute relative bin counts.
     * If {@code true}, the data count in each bin will be divided by the total
     * number of samples.
     * @param distance Distance.
     */
    public HitHistogram(boolean normalizeCount,
                        DistanceMeasure distance) {
        this.normalizeCount = normalizeCount;
        this.distance = distance;
    }

    /** {@inheritDoc} */
    public double[][] computeImage(NeuronSquareMesh2D map,
                                   Iterable<double[]> data) {
        final int nR = map.getNumberOfRows();
        final int nC = map.getNumberOfColumns();

        final LocationFinder finder = new LocationFinder(map);

        // Total number of samples.
        int numSamples = 0;
        // Hit bins.
        final double[][] hit = new double[nR][nC];

        for (double[] sample : data) {
            final Neuron best = MapUtils.findBest(sample, map, distance);

            final LocationFinder.Location loc = finder.getLocation(best);
            final int row = loc.getRow();
            final int col = loc.getColumn();
            hit[row][col] += 1;

            ++numSamples;
        }

        if (normalizeCount) {
            for (int r = 0; r < nR; r++) {
                for (int c = 0; c < nC; c++) {
                    hit[r][c] /= numSamples;
                }
            }
        }

        return hit;
    }
}
