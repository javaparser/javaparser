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

package org.apache.commons.math3.ml.neuralnet.oned;

import java.io.Serializable;
import java.io.ObjectInputStream;
import org.apache.commons.math3.ml.neuralnet.Network;
import org.apache.commons.math3.ml.neuralnet.FeatureInitializer;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;

/**
 * Neural network with the topology of a one-dimensional line.
 * Each neuron defines one point on the line.
 *
 * @since 3.3
 */
public class NeuronString implements Serializable {
    /** Serial version ID */
    private static final long serialVersionUID = 1L;
    /** Underlying network. */
    private final Network network;
    /** Number of neurons. */
    private final int size;
    /** Wrap. */
    private final boolean wrap;

    /**
     * Mapping of the 1D coordinate to the neuron identifiers
     * (attributed by the {@link #network} instance).
     */
    private final long[] identifiers;

    /**
     * Constructor with restricted access, solely used for deserialization.
     *
     * @param wrap Whether to wrap the dimension (i.e the first and last
     * neurons will be linked together).
     * @param featuresList Arrays that will initialize the features sets of
     * the network's neurons.
     * @throws NumberIsTooSmallException if {@code num < 2}.
     */
    NeuronString(boolean wrap,
                 double[][] featuresList) {
        size = featuresList.length;

        if (size < 2) {
            throw new NumberIsTooSmallException(size, 2, true);
        }

        this.wrap = wrap;

        final int fLen = featuresList[0].length;
        network = new Network(0, fLen);
        identifiers = new long[size];

        // Add neurons.
        for (int i = 0; i < size; i++) {
            identifiers[i] = network.createNeuron(featuresList[i]);
        }

        // Add links.
        createLinks();
    }

    /**
     * Creates a one-dimensional network:
     * Each neuron not located on the border of the mesh has two
     * neurons linked to it.
     * <br/>
     * The links are bi-directional.
     * Neurons created successively are neighbours (i.e. there are
     * links between them).
     * <br/>
     * The topology of the network can also be a circle (if the
     * dimension is wrapped).
     *
     * @param num Number of neurons.
     * @param wrap Whether to wrap the dimension (i.e the first and last
     * neurons will be linked together).
     * @param featureInit Arrays that will initialize the features sets of
     * the network's neurons.
     * @throws NumberIsTooSmallException if {@code num < 2}.
     */
    public NeuronString(int num,
                        boolean wrap,
                        FeatureInitializer[] featureInit) {
        if (num < 2) {
            throw new NumberIsTooSmallException(num, 2, true);
        }

        size = num;
        this.wrap = wrap;
        identifiers = new long[num];

        final int fLen = featureInit.length;
        network = new Network(0, fLen);

        // Add neurons.
        for (int i = 0; i < num; i++) {
            final double[] features = new double[fLen];
            for (int fIndex = 0; fIndex < fLen; fIndex++) {
                features[fIndex] = featureInit[fIndex].value();
            }
            identifiers[i] = network.createNeuron(features);
        }

        // Add links.
        createLinks();
    }

    /**
     * Retrieves the underlying network.
     * A reference is returned (enabling, for example, the network to be
     * trained).
     * This also implies that calling methods that modify the {@link Network}
     * topology may cause this class to become inconsistent.
     *
     * @return the network.
     */
    public Network getNetwork() {
        return network;
    }

    /**
     * Gets the number of neurons.
     *
     * @return the number of neurons.
     */
    public int getSize() {
        return size;
    }

    /**
     * Retrieves the features set from the neuron at location
     * {@code i} in the map.
     *
     * @param i Neuron index.
     * @return the features of the neuron at index {@code i}.
     * @throws OutOfRangeException if {@code i} is out of range.
     */
    public double[] getFeatures(int i) {
        if (i < 0 ||
            i >= size) {
            throw new OutOfRangeException(i, 0, size - 1);
        }

        return network.getNeuron(identifiers[i]).getFeatures();
    }

    /**
     * Creates the neighbour relationships between neurons.
     */
    private void createLinks() {
        for (int i = 0; i < size - 1; i++) {
            network.addLink(network.getNeuron(i), network.getNeuron(i + 1));
        }
        for (int i = size - 1; i > 0; i--) {
            network.addLink(network.getNeuron(i), network.getNeuron(i - 1));
        }
        if (wrap) {
            network.addLink(network.getNeuron(0), network.getNeuron(size - 1));
            network.addLink(network.getNeuron(size - 1), network.getNeuron(0));
        }
    }

    /**
     * Prevents proxy bypass.
     *
     * @param in Input stream.
     */
    private void readObject(ObjectInputStream in) {
        throw new IllegalStateException();
    }

    /**
     * Custom serialization.
     *
     * @return the proxy instance that will be actually serialized.
     */
    private Object writeReplace() {
        final double[][] featuresList = new double[size][];
        for (int i = 0; i < size; i++) {
            featuresList[i] = getFeatures(i);
        }

        return new SerializationProxy(wrap,
                                      featuresList);
    }

    /**
     * Serialization.
     */
    private static class SerializationProxy implements Serializable {
        /** Serializable. */
        private static final long serialVersionUID = 20130226L;
        /** Wrap. */
        private final boolean wrap;
        /** Neurons' features. */
        private final double[][] featuresList;

        /**
         * @param wrap Whether the dimension is wrapped.
         * @param featuresList List of neurons features.
         * {@code neuronList}.
         */
        SerializationProxy(boolean wrap,
                           double[][] featuresList) {
            this.wrap = wrap;
            this.featuresList = featuresList;
        }

        /**
         * Custom serialization.
         *
         * @return the {@link Neuron} for which this instance is the proxy.
         */
        private Object readResolve() {
            return new NeuronString(wrap,
                                    featuresList);
        }
    }
}
