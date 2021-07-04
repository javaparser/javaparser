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


/** This abstract class implements the WELL class of pseudo-random number generator
 * from Fran&ccedil;ois Panneton, Pierre L'Ecuyer and Makoto Matsumoto.

 * <p>This generator is described in a paper by Fran&ccedil;ois Panneton,
 * Pierre L'Ecuyer and Makoto Matsumoto <a
 * href="http://www.iro.umontreal.ca/~lecuyer/myftp/papers/wellrng.pdf">Improved
 * Long-Period Generators Based on Linear Recurrences Modulo 2</a> ACM
 * Transactions on Mathematical Software, 32, 1 (2006). The errata for the paper
 * are in <a href="http://www.iro.umontreal.ca/~lecuyer/myftp/papers/wellrng-errata.txt">wellrng-errata.txt</a>.</p>

 * @see <a href="http://www.iro.umontreal.ca/~panneton/WELLRNG.html">WELL Random number generator</a>
 * @since 2.2

 */
public abstract class AbstractWell extends BitsStreamGenerator implements Serializable {

    /** Serializable version identifier. */
    private static final long serialVersionUID = -817701723016583596L;

    /** Current index in the bytes pool. */
    protected int index;

    /** Bytes pool. */
    protected final int[] v;

    /** Index indirection table giving for each index its predecessor taking table size into account. */
    protected final int[] iRm1;

    /** Index indirection table giving for each index its second predecessor taking table size into account. */
    protected final int[] iRm2;

    /** Index indirection table giving for each index the value index + m1 taking table size into account. */
    protected final int[] i1;

    /** Index indirection table giving for each index the value index + m2 taking table size into account. */
    protected final int[] i2;

    /** Index indirection table giving for each index the value index + m3 taking table size into account. */
    protected final int[] i3;

    /** Creates a new random number generator.
     * <p>The instance is initialized using the current time plus the
     * system identity hash code of this instance as the seed.</p>
     * @param k number of bits in the pool (not necessarily a multiple of 32)
     * @param m1 first parameter of the algorithm
     * @param m2 second parameter of the algorithm
     * @param m3 third parameter of the algorithm
     */
    protected AbstractWell(final int k, final int m1, final int m2, final int m3) {
        this(k, m1, m2, m3, null);
    }

    /** Creates a new random number generator using a single int seed.
     * @param k number of bits in the pool (not necessarily a multiple of 32)
     * @param m1 first parameter of the algorithm
     * @param m2 second parameter of the algorithm
     * @param m3 third parameter of the algorithm
     * @param seed the initial seed (32 bits integer)
     */
    protected AbstractWell(final int k, final int m1, final int m2, final int m3, final int seed) {
        this(k, m1, m2, m3, new int[] { seed });
    }

    /** Creates a new random number generator using an int array seed.
     * @param k number of bits in the pool (not necessarily a multiple of 32)
     * @param m1 first parameter of the algorithm
     * @param m2 second parameter of the algorithm
     * @param m3 third parameter of the algorithm
     * @param seed the initial seed (32 bits integers array), if null
     * the seed of the generator will be related to the current time
     */
    protected AbstractWell(final int k, final int m1, final int m2, final int m3, final int[] seed) {

        // the bits pool contains k bits, k = r w - p where r is the number
        // of w bits blocks, w is the block size (always 32 in the original paper)
        // and p is the number of unused bits in the last block
        final int w = 32;
        final int r = (k + w - 1) / w;
        this.v      = new int[r];
        this.index  = 0;

        // precompute indirection index tables. These tables are used for optimizing access
        // they allow saving computations like "(j + r - 2) % r" with costly modulo operations
        iRm1 = new int[r];
        iRm2 = new int[r];
        i1   = new int[r];
        i2   = new int[r];
        i3   = new int[r];
        for (int j = 0; j < r; ++j) {
            iRm1[j] = (j + r - 1) % r;
            iRm2[j] = (j + r - 2) % r;
            i1[j]   = (j + m1)    % r;
            i2[j]   = (j + m2)    % r;
            i3[j]   = (j + m3)    % r;
        }

        // initialize the pool content
        setSeed(seed);

    }

    /** Creates a new random number generator using a single long seed.
     * @param k number of bits in the pool (not necessarily a multiple of 32)
     * @param m1 first parameter of the algorithm
     * @param m2 second parameter of the algorithm
     * @param m3 third parameter of the algorithm
     * @param seed the initial seed (64 bits integer)
     */
    protected AbstractWell(final int k, final int m1, final int m2, final int m3, final long seed) {
        this(k, m1, m2, m3, new int[] { (int) (seed >>> 32), (int) (seed & 0xffffffffl) });
    }

    /** Reinitialize the generator as if just built with the given int seed.
     * <p>The state of the generator is exactly the same as a new
     * generator built with the same seed.</p>
     * @param seed the initial seed (32 bits integer)
     */
    @Override
    public void setSeed(final int seed) {
        setSeed(new int[] { seed });
    }

    /** Reinitialize the generator as if just built with the given int array seed.
     * <p>The state of the generator is exactly the same as a new
     * generator built with the same seed.</p>
     * @param seed the initial seed (32 bits integers array). If null
     * the seed of the generator will be the system time plus the system identity
     * hash code of the instance.
     */
    @Override
    public void setSeed(final int[] seed) {
        if (seed == null) {
            setSeed(System.currentTimeMillis() + System.identityHashCode(this));
            return;
        }

        System.arraycopy(seed, 0, v, 0, FastMath.min(seed.length, v.length));

        if (seed.length < v.length) {
            for (int i = seed.length; i < v.length; ++i) {
                final long l = v[i - seed.length];
                v[i] = (int) ((1812433253l * (l ^ (l >> 30)) + i) & 0xffffffffL);
            }
        }

        index = 0;
        clear();  // Clear normal deviate cache
    }

    /** Reinitialize the generator as if just built with the given long seed.
     * <p>The state of the generator is exactly the same as a new
     * generator built with the same seed.</p>
     * @param seed the initial seed (64 bits integer)
     */
    @Override
    public void setSeed(final long seed) {
        setSeed(new int[] { (int) (seed >>> 32), (int) (seed & 0xffffffffl) });
    }

    /** {@inheritDoc} */
    @Override
    protected abstract int next(final int bits);

}
