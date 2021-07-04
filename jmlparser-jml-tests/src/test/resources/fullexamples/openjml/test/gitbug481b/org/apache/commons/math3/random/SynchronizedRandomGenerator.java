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
 * Any {@link RandomGenerator} implementation can be thread-safe if it
 * is used through an instance of this class.
 * This is achieved by enclosing calls to the methods of the actual
 * generator inside the overridden {@code synchronized} methods of this
 * class.
 *
 * @since 3.1
 */
public class SynchronizedRandomGenerator implements RandomGenerator {
    /** Object to which all calls will be delegated. */
    private final RandomGenerator wrapped;

    /**
     * Creates a synchronized wrapper for the given {@code RandomGenerator}
     * instance.
     *
     * @param rng Generator whose methods will be called through
     * their corresponding overridden synchronized version.
     * To ensure thread-safety, the wrapped generator <em>must</em>
     * not be used directly.
     */
    public SynchronizedRandomGenerator(RandomGenerator rng) {
        wrapped = rng;
    }

    /**
     * {@inheritDoc}
     */
    public synchronized void setSeed(int seed) {
        wrapped.setSeed(seed);
    }

    /**
     * {@inheritDoc}
     */
    public synchronized void setSeed(int[] seed) {
        wrapped.setSeed(seed);
    }

    /**
     * {@inheritDoc}
     */
    public synchronized void setSeed(long seed) {
        wrapped.setSeed(seed);
    }

    /**
     * {@inheritDoc}
     */
    public synchronized void nextBytes(byte[] bytes) {
        wrapped.nextBytes(bytes);
    }

    /**
     * {@inheritDoc}
     */
    public synchronized int nextInt() {
        return wrapped.nextInt();
    }

    /**
     * {@inheritDoc}
     */
    public synchronized int nextInt(int n) {
        return wrapped.nextInt(n);
    }

    /**
     * {@inheritDoc}
     */
    public synchronized long nextLong() {
        return wrapped.nextLong();
    }

    /**
     * {@inheritDoc}
     */
    public synchronized boolean nextBoolean() {
        return wrapped.nextBoolean();
    }

    /**
     * {@inheritDoc}
     */
    public synchronized float nextFloat() {
        return wrapped.nextFloat();
    }

    /**
     * {@inheritDoc}
     */
    public synchronized double nextDouble() {
        return wrapped.nextDouble();
    }

    /**
     * {@inheritDoc}
     */
    public synchronized double nextGaussian() {
        return wrapped.nextGaussian();
    }
}
