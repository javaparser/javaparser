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

import java.util.Collection;
import org.apache.commons.math3.ml.neuralnet.Neuron;
import org.apache.commons.math3.ml.neuralnet.Network;
import org.apache.commons.math3.ml.neuralnet.twod.NeuronSquareMesh2D;
import org.apache.commons.math3.ml.distance.DistanceMeasure;

/**
 * <a href="http://en.wikipedia.org/wiki/U-Matrix">U-Matrix</a>
 * visualization of high-dimensional data projection.
 * @since 3.6
 */
public class UnifiedDistanceMatrix implements MapVisualization {
    /** Whether to show distance between each pair of neighbouring units. */
    private final boolean individualDistances;
    /** Distance. */
    private final DistanceMeasure distance;

    /**
     * Simple constructor.
     *
     * @param individualDistances If {@code true}, the 8 individual
     * inter-units distances will be {@link #computeImage(NeuronSquareMesh2D)
     * computed}.  They will be stored in additional pixels around each of
     * the original units of the 2D-map.  The additional pixels that lie
     * along a "diagonal" are shared by <em>two</em> pairs of units: their
     * value will be set to the average distance between the units belonging
     * to each of the pairs.  The value zero will be stored in the pixel
     * corresponding to the location of a unit of the 2D-map.
     * <br>
     * If {@code false}, only the average distance between a unit and all its
     * neighbours will be computed (and stored in the pixel corresponding to
     * that unit of the 2D-map).  In that case, the number of neighbours taken
     * into account depends on the network's
     * {@link org.apache.commons.math3.ml.neuralnet.SquareNeighbourhood
     * neighbourhood type}.
     * @param distance Distance.
     */
    public UnifiedDistanceMatrix(boolean individualDistances,
                                 DistanceMeasure distance) {
        this.individualDistances = individualDistances;
        this.distance = distance;
    }

    /** {@inheritDoc} */
    public double[][] computeImage(NeuronSquareMesh2D map) {
        if (individualDistances) {
            return individualDistances(map);
        } else {
            return averageDistances(map);
        }
    }

    /**
     * Computes the distances between a unit of the map and its
     * neighbours.
     * The image will contain more pixels than the number of neurons
     * in the given {@code map} because each neuron has 8 neighbours.
     * The value zero will be stored in the pixels corresponding to
     * the location of a map unit.
     *
     * @param map Map.
     * @return an image representing the individual distances.
     */
    private double[][] individualDistances(NeuronSquareMesh2D map) {
        final int numRows = map.getNumberOfRows();
        final int numCols = map.getNumberOfColumns();

        final double[][] uMatrix = new double[numRows * 2 + 1][numCols * 2 + 1];

        // 1.
        // Fill right and bottom slots of each unit's location with the
        // distance between the current unit and each of the two neighbours,
        // respectively.
        for (int i = 0; i < numRows; i++) {
            // Current unit's row index in result image.
            final int iR = 2 * i + 1;

            for (int j = 0; j < numCols; j++) {
                // Current unit's column index in result image.
                final int jR = 2 * j + 1;

                final double[] current = map.getNeuron(i, j).getFeatures();
                Neuron neighbour;

                // Right neighbour.
                neighbour = map.getNeuron(i, j,
                                          NeuronSquareMesh2D.HorizontalDirection.RIGHT,
                                          NeuronSquareMesh2D.VerticalDirection.CENTER);
                if (neighbour != null) {
                    uMatrix[iR][jR + 1] = distance.compute(current,
                                                           neighbour.getFeatures());
                }

                // Bottom-center neighbour.
                neighbour = map.getNeuron(i, j,
                                          NeuronSquareMesh2D.HorizontalDirection.CENTER,
                                          NeuronSquareMesh2D.VerticalDirection.DOWN);
                if (neighbour != null) {
                    uMatrix[iR + 1][jR] = distance.compute(current,
                                                           neighbour.getFeatures());
                }
            }
        }

        // 2.
        // Fill the bottom-rigth slot of each unit's location with the average
        // of the distances between
        //  * the current unit and its bottom-right neighbour, and
        //  * the bottom-center neighbour and the right neighbour.
        for (int i = 0; i < numRows; i++) {
            // Current unit's row index in result image.
            final int iR = 2 * i + 1;

            for (int j = 0; j < numCols; j++) {
                // Current unit's column index in result image.
                final int jR = 2 * j + 1;

                final Neuron current = map.getNeuron(i, j);
                final Neuron right = map.getNeuron(i, j,
                                                   NeuronSquareMesh2D.HorizontalDirection.RIGHT,
                                                   NeuronSquareMesh2D.VerticalDirection.CENTER);
                final Neuron bottom = map.getNeuron(i, j,
                                                    NeuronSquareMesh2D.HorizontalDirection.CENTER,
                                                    NeuronSquareMesh2D.VerticalDirection.DOWN);
                final Neuron bottomRight = map.getNeuron(i, j,
                                                         NeuronSquareMesh2D.HorizontalDirection.RIGHT,
                                                         NeuronSquareMesh2D.VerticalDirection.DOWN);

                final double current2BottomRight = bottomRight == null ?
                    0 :
                    distance.compute(current.getFeatures(),
                                     bottomRight.getFeatures());
                final double right2Bottom = (right == null ||
                                             bottom == null) ?
                    0 :
                    distance.compute(right.getFeatures(),
                                     bottom.getFeatures());

                // Bottom-right slot.
                uMatrix[iR + 1][jR + 1] = 0.5 * (current2BottomRight + right2Bottom);
            }
        }

        // 3. Copy last row into first row.
        final int lastRow = uMatrix.length - 1;
        uMatrix[0] = uMatrix[lastRow];

        // 4.
        // Copy last column into first column.
        final int lastCol = uMatrix[0].length - 1;
        for (int r = 0; r < lastRow; r++) {
            uMatrix[r][0] = uMatrix[r][lastCol];
        }

        return uMatrix;
    }

    /**
     * Computes the distances between a unit of the map and its neighbours.
     *
     * @param map Map.
     * @return an image representing the average distances.
     */
    private double[][] averageDistances(NeuronSquareMesh2D map) {
        final int numRows = map.getNumberOfRows();
        final int numCols = map.getNumberOfColumns();
        final double[][] uMatrix = new double[numRows][numCols];

        final Network net = map.getNetwork();

        for (int i = 0; i < numRows; i++) {
            for (int j = 0; j < numCols; j++) {
                final Neuron neuron = map.getNeuron(i, j);
                final Collection<Neuron> neighbours = net.getNeighbours(neuron);
                final double[] features = neuron.getFeatures();

                double d = 0;
                int count = 0;
                for (Neuron n : neighbours) {
                    ++count;
                    d += distance.compute(features, n.getFeatures());
                }

                uMatrix[i][j] = d / count;
            }
        }

        return uMatrix;
    }
}
