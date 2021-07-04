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

import java.util.EventObject;

/**
 * The root class from which all events occurring while running an
 * {@link IterationManager} should be derived.
 *
 */
public class IterationEvent extends EventObject {
    /** */
    private static final long serialVersionUID = 20120128L;

    /** The number of iterations performed so far. */
    private final int iterations;

    /**
     * Creates a new instance of this class.
     *
     * @param source the iterative algorithm on which the event initially
     * occurred
     * @param iterations the number of iterations performed at the time
     * {@code this} event is created
     */
    public IterationEvent(final Object source, final int iterations) {
        super(source);
        this.iterations = iterations;
    }

    /**
     * Returns the number of iterations performed at the time {@code this} event
     * is created.
     *
     * @return the number of iterations performed
     */
    public int getIterations() {
        return iterations;
    }
 }
