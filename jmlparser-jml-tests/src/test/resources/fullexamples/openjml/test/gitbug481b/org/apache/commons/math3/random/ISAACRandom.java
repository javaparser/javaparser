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

import java.io.Serializable;

import org.apache.commons.math3.util.FastMath;

/**
 * <a href="http://burtleburtle.net/bob/rand/isaacafa.html">
 *  ISAAC: a fast cryptographic pseudo-random number generator</a>
 * <br/>
 * ISAAC (Indirection, Shift, Accumulate, Add, and Count) generates 32-bit
 * random numbers.
 * ISAAC has been designed to be cryptographically secure and is inspired
 * by RC4.
 * Cycles are guaranteed to be at least 2<sup>40</sup> values long, and they
 * are 2<sup>8295</sup> values long on average.
 * The results are uniformly distributed, unbiased, and unpredictable unless
 * you know the seed.
 * <br/>
 * This code is based (with minor changes and improvements) on the original
 * implementation of the algorithm by Bob Jenkins.
 * <br/>
 *
 * @since 3.0
 */
public class ISAACRandom extends BitsStreamGenerator implements Serializable {
    /** Serializable version identifier */
    private static final long serialVersionUID = 7288197941165002400L;
    /** Log of size of rsl[] and mem[] */
    private static final int SIZE_L = 8;
    /** Size of rsl[] and mem[] */
    private static final int SIZE = 1 << SIZE_L;
    /** Half-size of rsl[] and mem[] */
    private static final int H_SIZE = SIZE >> 1;
    /** For pseudo-random lookup */
    private static final int MASK = SIZE - 1 << 2;
    /** The golden ratio */
    private static final int GLD_RATIO = 0x9e3779b9;
    /** The results given to the user */
    private final int[] rsl = new int[SIZE];
    /** The internal state */
    private final int[] mem = new int[SIZE];
    /** Count through the results in rsl[] */
    private int count;
    /** Accumulator */
    private int isaacA;
    /** The last result */
    private int isaacB;
    /** Counter, guarantees cycle is at least 2^40 */
    private int isaacC;
    /** Service variable. */
    private final int[] arr = new int[8];
    /** Service variable. */
    private int isaacX;
    /** Service variable. */
    private int isaacI;
    /** Service variable. */
    private int isaacJ;


    /**
     * Creates a new ISAAC random number generator.
     * <br/>
     * The instance is initialized using a combination of the
     * current time and system hash code of the instance as the seed.
     */
    public ISAACRandom() {
        setSeed(System.currentTimeMillis() + System.identityHashCode(this));
    }

    /**
     * Creates a new ISAAC random number generator using a single long seed.
     *
     * @param seed Initial seed.
     */
    public ISAACRandom(long seed) {
        setSeed(seed);
    }

    /**
     * Creates a new ISAAC random number generator using an int array seed.
     *
     * @param seed Initial seed. If {@code null}, the seed will be related
     * to the current time.
     */
    public ISAACRandom(int[] seed) {
        setSeed(seed);
    }

    /** {@inheritDoc} */
    @Override
    public void setSeed(int seed) {
        setSeed(new int[]{seed});
    }

    /** {@inheritDoc} */
    @Override
    public void setSeed(long seed) {
        setSeed(new int[]{(int) (seed >>> 32), (int) (seed & 0xffffffffL)});
    }

    /** {@inheritDoc} */
    @Override
    public void setSeed(int[] seed) {
        if (seed == null) {
            setSeed(System.currentTimeMillis() + System.identityHashCode(this));
            return;
        }
        final int seedLen = seed.length;
        final int rslLen = rsl.length;
        System.arraycopy(seed, 0, rsl, 0, FastMath.min(seedLen, rslLen));
        if (seedLen < rslLen) {
            for (int j = seedLen; j < rslLen; j++) {
                long k = rsl[j - seedLen];
                rsl[j] = (int) (0x6c078965L * (k ^ k >> 30) + j & 0xffffffffL);
            }
        }
        initState();
    }

    /** {@inheritDoc} */
    @Override
    protected int next(int bits) {
        if (count < 0) {
            isaac();
            count = SIZE - 1;
        }
        return rsl[count--] >>> 32 - bits;
    }

    /** Generate 256 results */
    private void isaac() {
        isaacI = 0;
        isaacJ = H_SIZE;
        isaacB += ++isaacC;
        while (isaacI < H_SIZE) {
            isaac2();
        }
        isaacJ = 0;
        while (isaacJ < H_SIZE) {
            isaac2();
        }
    }

    /** Intermediate internal loop. */
    private void isaac2() {
        isaacX = mem[isaacI];
        isaacA ^= isaacA << 13;
        isaacA += mem[isaacJ++];
        isaac3();
        isaacX = mem[isaacI];
        isaacA ^= isaacA >>> 6;
        isaacA += mem[isaacJ++];
        isaac3();
        isaacX = mem[isaacI];
        isaacA ^= isaacA << 2;
        isaacA += mem[isaacJ++];
        isaac3();
        isaacX = mem[isaacI];
        isaacA ^= isaacA >>> 16;
        isaacA += mem[isaacJ++];
        isaac3();
    }

    /** Lowest level internal loop. */
    private void isaac3() {
        mem[isaacI] = mem[(isaacX & MASK) >> 2] + isaacA + isaacB;
        isaacB = mem[(mem[isaacI] >> SIZE_L & MASK) >> 2] + isaacX;
        rsl[isaacI++] = isaacB;
    }

    /** Initialize, or reinitialize, this instance of rand. */
    private void initState() {
        isaacA = 0;
        isaacB = 0;
        isaacC = 0;
        for (int j = 0; j < arr.length; j++) {
            arr[j] = GLD_RATIO;
        }
        for (int j = 0; j < 4; j++) {
            shuffle();
        }
        // fill in mem[] with messy stuff
        for (int j = 0; j < SIZE; j += 8) {
            arr[0] += rsl[j];
            arr[1] += rsl[j + 1];
            arr[2] += rsl[j + 2];
            arr[3] += rsl[j + 3];
            arr[4] += rsl[j + 4];
            arr[5] += rsl[j + 5];
            arr[6] += rsl[j + 6];
            arr[7] += rsl[j + 7];
            shuffle();
            setState(j);
        }
        // second pass makes all of seed affect all of mem
        for (int j = 0; j < SIZE; j += 8) {
            arr[0] += mem[j];
            arr[1] += mem[j + 1];
            arr[2] += mem[j + 2];
            arr[3] += mem[j + 3];
            arr[4] += mem[j + 4];
            arr[5] += mem[j + 5];
            arr[6] += mem[j + 6];
            arr[7] += mem[j + 7];
            shuffle();
            setState(j);
        }
        isaac();
        count = SIZE - 1;
        clear();
    }

    /** Shuffle array. */
    private void shuffle() {
        arr[0] ^= arr[1] << 11;
        arr[3] += arr[0];
        arr[1] += arr[2];
        arr[1] ^= arr[2] >>> 2;
        arr[4] += arr[1];
        arr[2] += arr[3];
        arr[2] ^= arr[3] << 8;
        arr[5] += arr[2];
        arr[3] += arr[4];
        arr[3] ^= arr[4] >>> 16;
        arr[6] += arr[3];
        arr[4] += arr[5];
        arr[4] ^= arr[5] << 10;
        arr[7] += arr[4];
        arr[5] += arr[6];
        arr[5] ^= arr[6] >>> 4;
        arr[0] += arr[5];
        arr[6] += arr[7];
        arr[6] ^= arr[7] << 8;
        arr[1] += arr[6];
        arr[7] += arr[0];
        arr[7] ^= arr[0] >>> 9;
        arr[2] += arr[7];
        arr[0] += arr[1];
    }

    /** Set the state by copying the internal arrays.
     *
     * @param start First index into {@link #mem} array.
     */
    private void setState(int start) {
        mem[start] = arr[0];
        mem[start + 1] = arr[1];
        mem[start + 2] = arr[2];
        mem[start + 3] = arr[3];
        mem[start + 4] = arr[4];
        mem[start + 5] = arr[5];
        mem[start + 6] = arr[6];
        mem[start + 7] = arr[7];
    }
}
