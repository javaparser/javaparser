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
 * Computes the quantization error histogram.
 * Each bin will contain the average of the distances between samples
 * mapped to the corresponding unit and the weight vector of that unit.
 * @since 3.6
 */
public class QuantizationError implements MapDataVisualization {
    /** Distance. */
    private final DistanceMeasure distance;

    /**
     * @param distance Distance.
     */
    public QuantizationError(DistanceMeasure distance) {
        this.distance = distance;
    }

    /** {@inheritDoc} */
    public double[][] computeImage(NeuronSquareMesh2D map,
                                   Iterable<double[]> data) {
        final int nR = map.getNumberOfRows();
        final int nC = map.getNumberOfColumns();

        final LocationFinder finder = new LocationFinder(map);

        // Hit bins.
        final int[][] hit = new int[nR][nC];
        // Error bins.
        final double[][] error = new double[nR][nC];

        for (double[] sample : data) {
            final Neuron best = MapUtils.findBest(sample, map, distance);

            final LocationFinder.Location loc = finder.getLocation(best);
            final int row = loc.getRow();
            final int col = loc.getColumn();
            hit[row][col] += 1;
            error[row][col] += distance.compute(sample, best.getFeatures());
        }

        for (int r = 0; r < nR; r++) {
            for (int c = 0; c < nC; c++) {
                final int count = hit[r][c];
                if (count != 0) {
                    error[r][c] /= count;
                }
            }
        }

        return error;
    }
}
