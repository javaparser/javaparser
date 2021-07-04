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

package org.apache.commons.math3.ml.neuralnet;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Comparator;

import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.ml.distance.DistanceMeasure;
import org.apache.commons.math3.ml.neuralnet.twod.NeuronSquareMesh2D;
import org.apache.commons.math3.util.Pair;

/**
 * Utilities for network maps.
 *
 * @since 3.3
 */
public class MapUtils {
    /**
     * Class contains only static methods.
     */
    private MapUtils() {}

    /**
     * Finds the neuron that best matches the given features.
     *
     * @param features Data.
     * @param neurons List of neurons to scan. If the list is empty
     * {@code null} will be returned.
     * @param distance Distance function. The neuron's features are
     * passed as the first argument to {@link DistanceMeasure#compute(double[],double[])}.
     * @return the neuron whose features are closest to the given data.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the size of the input is not compatible with the neurons features
     * size.
     */
    public static Neuron findBest(double[] features,
                                  Iterable<Neuron> neurons,
                                  DistanceMeasure distance) {
        Neuron best = null;
        double min = Double.POSITIVE_INFINITY;
        for (final Neuron n : neurons) {
            final double d = distance.compute(n.getFeatures(), features);
            if (d < min) {
                min = d;
                best = n;
            }
        }

        return best;
    }

    /**
     * Finds the two neurons that best match the given features.
     *
     * @param features Data.
     * @param neurons List of neurons to scan. If the list is empty
     * {@code null} will be returned.
     * @param distance Distance function. The neuron's features are
     * passed as the first argument to {@link DistanceMeasure#compute(double[],double[])}.
     * @return the two neurons whose features are closest to the given data.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the size of the input is not compatible with the neurons features
     * size.
     */
    public static Pair<Neuron, Neuron> findBestAndSecondBest(double[] features,
                                                             Iterable<Neuron> neurons,
                                                             DistanceMeasure distance) {
        Neuron[] best = { null, null };
        double[] min = { Double.POSITIVE_INFINITY,
                         Double.POSITIVE_INFINITY };
        for (final Neuron n : neurons) {
            final double d = distance.compute(n.getFeatures(), features);
            if (d < min[0]) {
                // Replace second best with old best.
                min[1] = min[0];
                best[1] = best[0];

                // Store current as new best.
                min[0] = d;
                best[0] = n;
            } else if (d < min[1]) {
                // Replace old second best with current.
                min[1] = d;
                best[1] = n;
            }
        }

        return new Pair<Neuron, Neuron>(best[0], best[1]);
    }

    /**
     * Creates a list of neurons sorted in increased order of the distance
     * to the given {@code features}.
     *
     * @param features Data.
     * @param neurons List of neurons to scan. If it is empty, an empty array
     * will be returned.
     * @param distance Distance function.
     * @return the neurons, sorted in increasing order of distance in data
     * space.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the size of the input is not compatible with the neurons features
     * size.
     *
     * @see #findBest(double[],Iterable,DistanceMeasure)
     * @see #findBestAndSecondBest(double[],Iterable,DistanceMeasure)
     *
     * @since 3.6
     */
    public static Neuron[] sort(double[] features,
                                Iterable<Neuron> neurons,
                                DistanceMeasure distance) {
        final List<PairNeuronDouble> list = new ArrayList<PairNeuronDouble>();

        for (final Neuron n : neurons) {
            final double d = distance.compute(n.getFeatures(), features);
            list.add(new PairNeuronDouble(n, d));
        }

        Collections.sort(list, PairNeuronDouble.COMPARATOR);

        final int len = list.size();
        final Neuron[] sorted = new Neuron[len];

        for (int i = 0; i < len; i++) {
            sorted[i] = list.get(i).getNeuron();
        }
        return sorted;
    }

    /**
     * Computes the <a href="http://en.wikipedia.org/wiki/U-Matrix">
     *  U-matrix</a> of a two-dimensional map.
     *
     * @param map Network.
     * @param distance Function to use for computing the average
     * distance from a neuron to its neighbours.
     * @return the matrix of average distances.
     */
    public static double[][] computeU(NeuronSquareMesh2D map,
                                      DistanceMeasure distance) {
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

    /**
     * Computes the "hit" histogram of a two-dimensional map.
     *
     * @param data Feature vectors.
     * @param map Network.
     * @param distance Function to use for determining the best matching unit.
     * @return the number of hits for each neuron in the map.
     */
    public static int[][] computeHitHistogram(Iterable<double[]> data,
                                              NeuronSquareMesh2D map,
                                              DistanceMeasure distance) {
        final HashMap<Neuron, Integer> hit = new HashMap<Neuron, Integer>();
        final Network net = map.getNetwork();

        for (double[] f : data) {
            final Neuron best = findBest(f, net, distance);
            final Integer count = hit.get(best);
            if (count == null) {
                hit.put(best, 1);
            } else {
                hit.put(best, count + 1);
            }
        }

        // Copy the histogram data into a 2D map.
        final int numRows = map.getNumberOfRows();
        final int numCols = map.getNumberOfColumns();
        final int[][] histo = new int[numRows][numCols];

        for (int i = 0; i < numRows; i++) {
            for (int j = 0; j < numCols; j++) {
                final Neuron neuron = map.getNeuron(i, j);
                final Integer count = hit.get(neuron);
                if (count == null) {
                    histo[i][j] = 0;
                } else {
                    histo[i][j] = count;
                }
            }
        }

        return histo;
    }

    /**
     * Computes the quantization error.
     * The quantization error is the average distance between a feature vector
     * and its "best matching unit" (closest neuron).
     *
     * @param data Feature vectors.
     * @param neurons List of neurons to scan.
     * @param distance Distance function.
     * @return the error.
     * @throws NoDataException if {@code data} is empty.
     */
    public static double computeQuantizationError(Iterable<double[]> data,
                                                  Iterable<Neuron> neurons,
                                                  DistanceMeasure distance) {
        double d = 0;
        int count = 0;
        for (double[] f : data) {
            ++count;
            d += distance.compute(f, findBest(f, neurons, distance).getFeatures());
        }

        if (count == 0) {
            throw new NoDataException();
        }

        return d / count;
    }

    /**
     * Computes the topographic error.
     * The topographic error is the proportion of data for which first and
     * second best matching units are not adjacent in the map.
     *
     * @param data Feature vectors.
     * @param net Network.
     * @param distance Distance function.
     * @return the error.
     * @throws NoDataException if {@code data} is empty.
     */
    public static double computeTopographicError(Iterable<double[]> data,
                                                 Network net,
                                                 DistanceMeasure distance) {
        int notAdjacentCount = 0;
        int count = 0;
        for (double[] f : data) {
            ++count;
            final Pair<Neuron, Neuron> p = findBestAndSecondBest(f, net, distance);
            if (!net.getNeighbours(p.getFirst()).contains(p.getSecond())) {
                // Increment count if first and second best matching units
                // are not neighbours.
                ++notAdjacentCount;
            }
        }

        if (count == 0) {
            throw new NoDataException();
        }

        return ((double) notAdjacentCount) / count;
    }

    /**
     * Helper data structure holding a (Neuron, double) pair.
     */
    private static class PairNeuronDouble {
        /** Comparator. */
        static final Comparator<PairNeuronDouble> COMPARATOR
            = new Comparator<PairNeuronDouble>() {
            /** {@inheritDoc} */
            public int compare(PairNeuronDouble o1,
                               PairNeuronDouble o2) {
                return Double.compare(o1.value, o2.value);
            }
        };
        /** Key. */
        private final Neuron neuron;
        /** Value. */
        private final double value;

        /**
         * @param neuron Neuron.
         * @param value Value.
         */
        PairNeuronDouble(Neuron neuron, double value) {
            this.neuron = neuron;
            this.value = value;
        }

        /** @return the neuron. */
        public Neuron getNeuron() {
            return neuron;
        }

    }
}
