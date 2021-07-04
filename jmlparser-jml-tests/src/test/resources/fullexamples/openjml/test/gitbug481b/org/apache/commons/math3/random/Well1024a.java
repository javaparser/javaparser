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


/** This class implements the WELL1024a pseudo-random number generator
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
public class Well1024a extends AbstractWell {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 5680173464174485492L;

    /** Number of bits in the pool. */
    private static final int K = 1024;

    /** First parameter of the algorithm. */
    private static final int M1 = 3;

    /** Second parameter of the algorithm. */
    private static final int M2 = 24;

    /** Third parameter of the algorithm. */
    private static final int M3 = 10;

    /** Creates a new random number generator.
     * <p>The instance is initialized using the current time as the
     * seed.</p>
     */
    public Well1024a() {
        super(K, M1, M2, M3);
    }

    /** Creates a new random number generator using a single int seed.
     * @param seed the initial seed (32 bits integer)
     */
    public Well1024a(int seed) {
        super(K, M1, M2, M3, seed);
    }

    /** Creates a new random number generator using an int array seed.
     * @param seed the initial seed (32 bits integers array), if null
     * the seed of the generator will be related to the current time
     */
    public Well1024a(int[] seed) {
        super(K, M1, M2, M3, seed);
    }

    /** Creates a new random number generator using a single long seed.
     * @param seed the initial seed (64 bits integer)
     */
    public Well1024a(long seed) {
        super(K, M1, M2, M3, seed);
    }

    /** {@inheritDoc} */
    @Override
    protected int next(final int bits) {

        final int indexRm1 = iRm1[index];

        final int v0       = v[index];
        final int vM1      = v[i1[index]];
        final int vM2      = v[i2[index]];
        final int vM3      = v[i3[index]];

        final int z0 = v[indexRm1];
        final int z1 = v0  ^ (vM1 ^ (vM1 >>> 8));
        final int z2 = (vM2 ^ (vM2 << 19)) ^ (vM3 ^ (vM3 << 14));
        final int z3 = z1      ^ z2;
        final int z4 = (z0 ^ (z0 << 11)) ^ (z1 ^ (z1 << 7)) ^ (z2 ^ (z2 << 13));

        v[index]     = z3;
        v[indexRm1]  = z4;
        index        = indexRm1;

        return z4 >>> (32 - bits);

    }
}
