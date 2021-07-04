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
package org.apache.commons.math3.util;

import java.util.Collection;
import java.util.concurrent.CopyOnWriteArrayList;

import org.apache.commons.math3.exception.MaxCountExceededException;

/**
 * This abstract class provides a general framework for managing iterative
 * algorithms. The maximum number of iterations can be set, and methods are
 * provided to monitor the current iteration count. A lightweight event
 * framework is also provided.
 *
 */
public class IterationManager {

    /** Keeps a count of the number of iterations. */
    private IntegerSequence.Incrementor iterations;

    /** The collection of all listeners attached to this iterative algorithm. */
    private final Collection<IterationListener> listeners;

    /**
     * Creates a new instance of this class.
     *
     * @param maxIterations the maximum number of iterations
     */
    public IterationManager(final int maxIterations) {
        this.iterations = IntegerSequence.Incrementor.create().withMaximalCount(maxIterations);
        this.listeners = new CopyOnWriteArrayList<IterationListener>();
    }

    /**
     * Creates a new instance of this class.
     *
     * @param maxIterations the maximum number of iterations
     * @param callBack the function to be called when the maximum number of
     * iterations has been reached
     * @throws org.apache.commons.math3.exception.NullArgumentException if {@code callBack} is {@code null}
     * @since 3.1
     * @deprecated as of 3.6, replaced with {@link #IterationManager(int,
     * org.apache.commons.math3.util.IntegerSequence.Incrementor.MaxCountExceededCallback)}
     */
    @Deprecated
    public IterationManager(final int maxIterations,
                            final Incrementor.MaxCountExceededCallback callBack) {
        this(maxIterations, new IntegerSequence.Incrementor.MaxCountExceededCallback() {
            /** {@inheritDoc} */
            public void trigger(final int maximalCount) throws MaxCountExceededException {
                callBack.trigger(maximalCount);
            }
        });
    }

    /**
     * Creates a new instance of this class.
     *
     * @param maxIterations the maximum number of iterations
     * @param callBack the function to be called when the maximum number of
     * iterations has been reached
     * @throws org.apache.commons.math3.exception.NullArgumentException if {@code callBack} is {@code null}
     * @since 3.6
     */
    public IterationManager(final int maxIterations,
                            final IntegerSequence.Incrementor.MaxCountExceededCallback callBack) {
        this.iterations = IntegerSequence.Incrementor.create().withMaximalCount(maxIterations).withCallback(callBack);
        this.listeners = new CopyOnWriteArrayList<IterationListener>();
    }

    /**
     * Attaches a listener to this manager.
     *
     * @param listener A {@code IterationListener} object.
     */
    public void addIterationListener(final IterationListener listener) {
        listeners.add(listener);
    }

    /**
     * Informs all registered listeners that the initial phase (prior to the
     * main iteration loop) has been completed.
     *
     * @param e The {@link IterationEvent} object.
     */
    public void fireInitializationEvent(final IterationEvent e) {
        for (IterationListener l : listeners) {
            l.initializationPerformed(e);
        }
    }

    /**
     * Informs all registered listeners that a new iteration (in the main
     * iteration loop) has been performed.
     *
     * @param e The {@link IterationEvent} object.
     */
    public void fireIterationPerformedEvent(final IterationEvent e) {
        for (IterationListener l : listeners) {
            l.iterationPerformed(e);
        }
    }

    /**
     * Informs all registered listeners that a new iteration (in the main
     * iteration loop) has been started.
     *
     * @param e The {@link IterationEvent} object.
     */
    public void fireIterationStartedEvent(final IterationEvent e) {
        for (IterationListener l : listeners) {
            l.iterationStarted(e);
        }
    }

    /**
     * Informs all registered listeners that the final phase (post-iterations)
     * has been completed.
     *
     * @param e The {@link IterationEvent} object.
     */
    public void fireTerminationEvent(final IterationEvent e) {
        for (IterationListener l : listeners) {
            l.terminationPerformed(e);
        }
    }

    /**
     * Returns the number of iterations of this solver, 0 if no iterations has
     * been performed yet.
     *
     * @return the number of iterations.
     */
    public int getIterations() {
        return iterations.getCount();
    }

    /**
     * Returns the maximum number of iterations.
     *
     * @return the maximum number of iterations.
     */
    public int getMaxIterations() {
        return iterations.getMaximalCount();
    }

    /**
     * Increments the iteration count by one, and throws an exception if the
     * maximum number of iterations is reached. This method should be called at
     * the beginning of a new iteration.
     *
     * @throws MaxCountExceededException if the maximum number of iterations is
     * reached.
     */
    public void incrementIterationCount()
        throws MaxCountExceededException {
        iterations.increment();
    }

    /**
     * Removes the specified iteration listener from the list of listeners
     * currently attached to {@code this} object. Attempting to remove a
     * listener which was <em>not</em> previously registered does not cause any
     * error.
     *
     * @param listener The {@link IterationListener} to be removed.
     */
    public void removeIterationListener(final IterationListener listener) {
        listeners.remove(listener);
    }

    /**
     * Sets the iteration count to 0. This method must be called during the
     * initial phase.
     */
    public void resetIterationCount() {
        iterations = iterations.withStart(0);
    }
}
