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

import java.io.Serializable;
import java.io.ObjectInputStream;
import java.util.concurrent.atomic.AtomicReference;
import java.util.concurrent.atomic.AtomicLong;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.util.Precision;


/**
 * Describes a neuron element of a neural network.
 *
 * This class aims to be thread-safe.
 *
 * @since 3.3
 */
public class Neuron implements Serializable {
    /** Serializable. */
    private static final long serialVersionUID = 20130207L;
    /** Identifier. */
    private final long identifier;
    /** Length of the feature set. */
    private final int size;
    /** Neuron data. */
    private final AtomicReference<double[]> features;
    /** Number of attempts to update a neuron. */
    private final AtomicLong numberOfAttemptedUpdates = new AtomicLong(0);
    /** Number of successful updates  of a neuron. */
    private final AtomicLong numberOfSuccessfulUpdates = new AtomicLong(0);

    /**
     * Creates a neuron.
     * The size of the feature set is fixed to the length of the given
     * argument.
     * <br/>
     * Constructor is package-private: Neurons must be
     * {@link Network#createNeuron(double[]) created} by the network
     * instance to which they will belong.
     *
     * @param identifier Identifier (assigned by the {@link Network}).
     * @param features Initial values of the feature set.
     */
    Neuron(long identifier,
           double[] features) {
        this.identifier = identifier;
        this.size = features.length;
        this.features = new AtomicReference<double[]>(features.clone());
    }

    /**
     * Performs a deep copy of this instance.
     * Upon return, the copied and original instances will be independent:
     * Updating one will not affect the other.
     *
     * @return a new instance with the same state as this instance.
     * @since 3.6
     */
    public synchronized Neuron copy() {
        final Neuron copy = new Neuron(getIdentifier(),
                                       getFeatures());
        copy.numberOfAttemptedUpdates.set(numberOfAttemptedUpdates.get());
        copy.numberOfSuccessfulUpdates.set(numberOfSuccessfulUpdates.get());

        return copy;
    }

    /**
     * Gets the neuron's identifier.
     *
     * @return the identifier.
     */
    public long getIdentifier() {
        return identifier;
    }

    /**
     * Gets the length of the feature set.
     *
     * @return the number of features.
     */
    public int getSize() {
        return size;
    }

    /**
     * Gets the neuron's features.
     *
     * @return a copy of the neuron's features.
     */
    public double[] getFeatures() {
        return features.get().clone();
    }

    /**
     * Tries to atomically update the neuron's features.
     * Update will be performed only if the expected values match the
     * current values.<br/>
     * In effect, when concurrent threads call this method, the state
     * could be modified by one, so that it does not correspond to the
     * the state assumed by another.
     * Typically, a caller {@link #getFeatures() retrieves the current state},
     * and uses it to compute the new state.
     * During this computation, another thread might have done the same
     * thing, and updated the state: If the current thread were to proceed
     * with its own update, it would overwrite the new state (which might
     * already have been used by yet other threads).
     * To prevent this, the method does not perform the update when a
     * concurrent modification has been detected, and returns {@code false}.
     * When this happens, the caller should fetch the new current state,
     * redo its computation, and call this method again.
     *
     * @param expect Current values of the features, as assumed by the caller.
     * Update will never succeed if the contents of this array does not match
     * the values returned by {@link #getFeatures()}.
     * @param update Features's new values.
     * @return {@code true} if the update was successful, {@code false}
     * otherwise.
     * @throws DimensionMismatchException if the length of {@code update} is
     * not the same as specified in the {@link #Neuron(long,double[])
     * constructor}.
     */
    public boolean compareAndSetFeatures(double[] expect,
                                         double[] update) {
        if (update.length != size) {
            throw new DimensionMismatchException(update.length, size);
        }

        // Get the internal reference. Note that this must not be a copy;
        // otherwise the "compareAndSet" below will always fail.
        final double[] current = features.get();
        if (!containSameValues(current, expect)) {
            // Some other thread already modified the state.
            return false;
        }

        // Increment attempt counter.
        numberOfAttemptedUpdates.incrementAndGet();

        if (features.compareAndSet(current, update.clone())) {
            // The current thread could atomically update the state (attempt succeeded).
            numberOfSuccessfulUpdates.incrementAndGet();
            return true;
        } else {
            // Some other thread came first (attempt failed).
            return false;
        }
    }

    /**
     * Retrieves the number of calls to the
     * {@link #compareAndSetFeatures(double[],double[]) compareAndSetFeatures}
     * method.
     * Note that if the caller wants to use this method in combination with
     * {@link #getNumberOfSuccessfulUpdates()}, additional synchronization
     * may be required to ensure consistency.
     *
     * @return the number of update attempts.
     * @since 3.6
     */
    public long getNumberOfAttemptedUpdates() {
        return numberOfAttemptedUpdates.get();
    }

    /**
     * Retrieves the number of successful calls to the
     * {@link #compareAndSetFeatures(double[],double[]) compareAndSetFeatures}
     * method.
     * Note that if the caller wants to use this method in combination with
     * {@link #getNumberOfAttemptedUpdates()}, additional synchronization
     * may be required to ensure consistency.
     *
     * @return the number of successful updates.
     * @since 3.6
     */
    public long getNumberOfSuccessfulUpdates() {
        return numberOfSuccessfulUpdates.get();
    }

    /**
     * Checks whether the contents of both arrays is the same.
     *
     * @param current Current values.
     * @param expect Expected values.
     * @throws DimensionMismatchException if the length of {@code expected}
     * is not the same as specified in the {@link #Neuron(long,double[])
     * constructor}.
     * @return {@code true} if the arrays contain the same values.
     */
    private boolean containSameValues(double[] current,
                                      double[] expect) {
        if (expect.length != size) {
            throw new DimensionMismatchException(expect.length, size);
        }

        for (int i = 0; i < size; i++) {
            if (!Precision.equals(current[i], expect[i])) {
                return false;
            }
        }
        return true;
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
        return new SerializationProxy(identifier,
                                      features.get());
    }

    /**
     * Serialization.
     */
    private static class SerializationProxy implements Serializable {
        /** Serializable. */
        private static final long serialVersionUID = 20130207L;
        /** Features. */
        private final double[] features;
        /** Identifier. */
        private final long identifier;

        /**
         * @param identifier Identifier.
         * @param features Features.
         */
        SerializationProxy(long identifier,
                           double[] features) {
            this.identifier = identifier;
            this.features = features;
        }

        /**
         * Custom serialization.
         *
         * @return the {@link Neuron} for which this instance is the proxy.
         */
        private Object readResolve() {
            return new Neuron(identifier,
                              features);
        }
    }
}
