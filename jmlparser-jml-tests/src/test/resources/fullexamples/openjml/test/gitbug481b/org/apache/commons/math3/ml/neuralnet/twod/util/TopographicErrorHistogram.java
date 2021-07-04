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
import org.apache.commons.math3.ml.neuralnet.Network;
import org.apache.commons.math3.ml.neuralnet.twod.NeuronSquareMesh2D;
import org.apache.commons.math3.ml.distance.DistanceMeasure;
import org.apache.commons.math3.util.Pair;

/**
 * Computes the topographic error histogram.
 * Each bin will contain the number of data for which the first and
 * second best matching units are not adjacent in the map.
 * @since 3.6
 */
public class TopographicErrorHistogram implements MapDataVisualization {
    /** Distance. */
    private final DistanceMeasure distance;
    /** Whether to compute relative bin counts. */
    private final boolean relativeCount;

    /**
     * @param relativeCount Whether to compute relative bin counts.
     * If {@code true}, the data count in each bin will be divided by the total
     * number of samples mapped to the neuron represented by that bin.
     * @param distance Distance.
     */
    public TopographicErrorHistogram(boolean relativeCount,
                                     DistanceMeasure distance) {
        this.relativeCount = relativeCount;
        this.distance = distance;
    }

    /** {@inheritDoc} */
    public double[][] computeImage(NeuronSquareMesh2D map,
                                   Iterable<double[]> data) {
        final int nR = map.getNumberOfRows();
        final int nC = map.getNumberOfColumns();

        final Network net = map.getNetwork();
        final LocationFinder finder = new LocationFinder(map);

        // Hit bins.
        final int[][] hit = new int[nR][nC];
        // Error bins.
        final double[][] error = new double[nR][nC];

        for (double[] sample : data) {
            final Pair<Neuron, Neuron> p = MapUtils.findBestAndSecondBest(sample, map, distance);
            final Neuron best = p.getFirst();

            final LocationFinder.Location loc = finder.getLocation(best);
            final int row = loc.getRow();
            final int col = loc.getColumn();
            hit[row][col] += 1;

            if (!net.getNeighbours(best).contains(p.getSecond())) {
                // Increment count if first and second best matching units
                // are not neighbours.
                error[row][col] += 1;
            }
        }

        if (relativeCount) {
            for (int r = 0; r < nR; r++) {
                for (int c = 0; c < nC; c++) {
                    error[r][c] /= hit[r][c];
                }
            }
        }

        return error;
    }
}
