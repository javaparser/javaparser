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

package org.apache.commons.math3.random;

/**
 * This class is a gaussian normalized random generator for scalars.
 * <p>This class is a simple wrapper around the {@link
 * RandomGenerator#nextGaussian} method.</p>
 * @since 1.2
 */

public class GaussianRandomGenerator implements NormalizedRandomGenerator {

    /** Underlying generator. */
    private final RandomGenerator generator;

    /** Create a new generator.
     * @param generator underlying random generator to use
     */
    public GaussianRandomGenerator(final RandomGenerator generator) {
        this.generator = generator;
    }

    /** Generate a random scalar with null mean and unit standard deviation.
     * @return a random scalar with null mean and unit standard deviation
     */
    public double nextNormalizedDouble() {
        return generator.nextGaussian();
    }

}
