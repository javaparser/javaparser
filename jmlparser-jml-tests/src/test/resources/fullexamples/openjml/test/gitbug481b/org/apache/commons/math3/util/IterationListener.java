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

import java.util.EventListener;

/**
 * The listener interface for receiving events occurring in an iterative
 * algorithm.
 *
 */
public interface IterationListener extends EventListener {
    /**
     * Invoked after completion of the initial phase of the iterative algorithm
     * (prior to the main iteration loop).
     *
     * @param e The {@link IterationEvent} object.
     */
    void initializationPerformed(IterationEvent e);

    /**
     * Invoked each time an iteration is completed (in the main iteration loop).
     *
     * @param e The {@link IterationEvent} object.
     */
    void iterationPerformed(IterationEvent e);

    /**
     * Invoked each time a new iteration is completed (in the main iteration
     * loop).
     *
     * @param e The {@link IterationEvent} object.
     */
    void iterationStarted(IterationEvent e);

    /**
     * Invoked after completion of the operations which occur after breaking out
     * of the main iteration loop.
     *
     * @param e The {@link IterationEvent} object.
     */
    void terminationPerformed(IterationEvent e);
}
