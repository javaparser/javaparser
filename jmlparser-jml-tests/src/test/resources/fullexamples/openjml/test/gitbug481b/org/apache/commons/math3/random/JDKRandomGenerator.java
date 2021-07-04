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

import java.util.Random;

/**
 * Extension of <code>java.util.Random</code> to implement
 * {@link RandomGenerator}.
 *
 * @since 1.1
 */
public class JDKRandomGenerator extends Random implements RandomGenerator {

    /** Serializable version identifier. */
    private static final long serialVersionUID = -7745277476784028798L;

    /**
     * Create a new JDKRandomGenerator with a default seed.
     */
    public JDKRandomGenerator() {
        super();
    }

    /**
     * Create a new JDKRandomGenerator with the given seed.
     *
     * @param seed initial seed
     * @since 3.6
     */
    public JDKRandomGenerator(int seed) {
        setSeed(seed);
    }

    /** {@inheritDoc} */
    public void setSeed(int seed) {
        setSeed((long) seed);
    }

    /** {@inheritDoc} */
    public void setSeed(int[] seed) {
        setSeed(RandomGeneratorFactory.convertToLong(seed));
    }
}
