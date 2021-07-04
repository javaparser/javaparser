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

import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.util.FastMath;

/** Base class for random number generators that generates bits streams.
 *
 * @since 2.0
 */
public abstract class BitsStreamGenerator
    implements RandomGenerator,
               Serializable {
    /** Serializable version identifier */
    private static final long serialVersionUID = 20130104L;
    /** Next gaussian. */
    private double nextGaussian;

    /**
     * Creates a new random number generator.
     */
    public BitsStreamGenerator() {
        nextGaussian = Double.NaN;
    }

    /** {@inheritDoc} */
    public abstract void setSeed(int seed);

    /** {@inheritDoc} */
    public abstract void setSeed(int[] seed);

    /** {@inheritDoc} */
    public abstract void setSeed(long seed);

    /** Generate next pseudorandom number.
     * <p>This method is the core generation algorithm. It is used by all the
     * public generation methods for the various primitive types {@link
     * #nextBoolean()}, {@link #nextBytes(byte[])}, {@link #nextDouble()},
     * {@link #nextFloat()}, {@link #nextGaussian()}, {@link #nextInt()},
     * {@link #next(int)} and {@link #nextLong()}.</p>
     * @param bits number of random bits to produce
     * @return random bits generated
     */
    protected abstract int next(int bits);

    /** {@inheritDoc} */
    public boolean nextBoolean() {
        return next(1) != 0;
    }

    /** {@inheritDoc} */
    public double nextDouble() {
        final long high = ((long) next(26)) << 26;
        final int  low  = next(26);
        return (high | low) * 0x1.0p-52d;
    }

    /** {@inheritDoc} */
    public float nextFloat() {
        return next(23) * 0x1.0p-23f;
    }

    /** {@inheritDoc} */
    public double nextGaussian() {

        final double random;
        if (Double.isNaN(nextGaussian)) {
            // generate a new pair of gaussian numbers
            final double x = nextDouble();
            final double y = nextDouble();
            final double alpha = 2 * FastMath.PI * x;
            final double r      = FastMath.sqrt(-2 * FastMath.log(y));
            random       = r * FastMath.cos(alpha);
            nextGaussian = r * FastMath.sin(alpha);
        } else {
            // use the second element of the pair already generated
            random = nextGaussian;
            nextGaussian = Double.NaN;
        }

        return random;

    }

    /** {@inheritDoc} */
    public int nextInt() {
        return next(32);
    }

    /**
     * {@inheritDoc}
     * <p>This default implementation is copied from Apache Harmony
     * java.util.Random (r929253).</p>
     *
     * <p>Implementation notes: <ul>
     * <li>If n is a power of 2, this method returns
     * {@code (int) ((n * (long) next(31)) >> 31)}.</li>
     *
     * <li>If n is not a power of 2, what is returned is {@code next(31) % n}
     * with {@code next(31)} values rejected (i.e. regenerated) until a
     * value that is larger than the remainder of {@code Integer.MAX_VALUE / n}
     * is generated. Rejection of this initial segment is necessary to ensure
     * a uniform distribution.</li></ul></p>
     */
    public int nextInt(int n) throws IllegalArgumentException {
        if (n > 0) {
            if ((n & -n) == n) {
                return (int) ((n * (long) next(31)) >> 31);
            }
            int bits;
            int val;
            do {
                bits = next(31);
                val = bits % n;
            } while (bits - val + (n - 1) < 0);
            return val;
        }
        throw new NotStrictlyPositiveException(n);
    }

    /** {@inheritDoc} */
    public long nextLong() {
        final long high  = ((long) next(32)) << 32;
        final long  low  = ((long) next(32)) & 0xffffffffL;
        return high | low;
    }

    /**
     * Returns a pseudorandom, uniformly distributed {@code long} value
     * between 0 (inclusive) and the specified value (exclusive), drawn from
     * this random number generator's sequence.
     *
     * @param n the bound on the random number to be returned.  Must be
     * positive.
     * @return  a pseudorandom, uniformly distributed {@code long}
     * value between 0 (inclusive) and n (exclusive).
     * @throws IllegalArgumentException  if n is not positive.
     */
    public long nextLong(long n) throws IllegalArgumentException {
        if (n > 0) {
            long bits;
            long val;
            do {
                bits = ((long) next(31)) << 32;
                bits |= ((long) next(32)) & 0xffffffffL;
                val  = bits % n;
            } while (bits - val + (n - 1) < 0);
            return val;
        }
        throw new NotStrictlyPositiveException(n);
    }

    /**
     * Clears the cache used by the default implementation of
     * {@link #nextGaussian}.
     */
    public void clear() {
        nextGaussian = Double.NaN;
    }

    /**
     * Generates random bytes and places them into a user-supplied array.
     *
     * <p>
     * The array is filled with bytes extracted from random integers.
     * This implies that the number of random bytes generated may be larger than
     * the length of the byte array.
     * </p>
     *
     * @param bytes Array in which to put the generated bytes. Cannot be {@code null}.
     */
    public void nextBytes(byte[] bytes) {
        nextBytesFill(bytes, 0, bytes.length);
    }

    /**
     * Generates random bytes and places them into a user-supplied array.
     *
     * <p>
     * The array is filled with bytes extracted from random integers.
     * This implies that the number of random bytes generated may be larger than
     * the length of the byte array.
     * </p>
     *
     * @param bytes Array in which to put the generated bytes. Cannot be {@code null}.
     * @param start Index at which to start inserting the generated bytes.
     * @param len Number of bytes to insert.
     * @throws OutOfRangeException if {@code start < 0} or {@code start >= bytes.length}.
     * @throws OutOfRangeException if {@code len < 0} or {@code len > bytes.length - start}.
     */
    public void nextBytes(byte[] bytes,
                          int start,
                          int len) {
        if (start < 0 ||
            start >= bytes.length) {
            throw new OutOfRangeException(start, 0, bytes.length);
        }
        if (len < 0 ||
            len > bytes.length - start) {
            throw new OutOfRangeException(len, 0, bytes.length - start);
        }

        nextBytesFill(bytes, start, len);
    }

    /**
     * Generates random bytes and places them into a user-supplied array.
     *
     * <p>
     * The array is filled with bytes extracted from random integers.
     * This implies that the number of random bytes generated may be larger than
     * the length of the byte array.
     * </p>
     *
     * @param bytes Array in which to put the generated bytes. Cannot be {@code null}.
     * @param start Index at which to start inserting the generated bytes.
     * @param len Number of bytes to insert.
     */
    private void nextBytesFill(byte[] bytes,
                               int start,
                               int len) {
        int index = start; // Index of first insertion.

        // Index of first insertion plus multiple 4 part of length (i.e. length
        // with two least significant bits unset).
        final int indexLoopLimit = index + (len & 0x7ffffffc);

        // Start filling in the byte array, 4 bytes at a time.
        while (index < indexLoopLimit) {
            final int random = next(32);
            bytes[index++] = (byte) random;
            bytes[index++] = (byte) (random >>> 8);
            bytes[index++] = (byte) (random >>> 16);
            bytes[index++] = (byte) (random >>> 24);
        }

        final int indexLimit = start + len; // Index of last insertion + 1.

        // Fill in the remaining bytes.
        if (index < indexLimit) {
            int random = next(32);
            while (true) {
                bytes[index++] = (byte) random;
                if (index < indexLimit) {
                    random >>>= 8;
                } else {
                    break;
                }
            }
        }
    }
}
