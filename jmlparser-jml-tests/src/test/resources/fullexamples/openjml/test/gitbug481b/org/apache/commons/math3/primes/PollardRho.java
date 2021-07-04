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
package org.apache.commons.math3.primes;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.util.FastMath;

/**
 * Implementation of the Pollard's rho factorization algorithm.
 * @since 3.2
 */
class PollardRho {

    /**
     * Hide utility class.
     */
    private PollardRho() {
    }

    /**
     * Factorization using Pollard's rho algorithm.
     * @param n number to factors, must be &gt; 0
     * @return the list of prime factors of n.
     */
    public static List<Integer> primeFactors(int n) {
        final List<Integer> factors = new ArrayList<Integer>();

        n = SmallPrimes.smallTrialDivision(n, factors);
        if (1 == n) {
            return factors;
        }

        if (SmallPrimes.millerRabinPrimeTest(n)) {
            factors.add(n);
            return factors;
        }

        int divisor = rhoBrent(n);
        factors.add(divisor);
        factors.add(n / divisor);
        return factors;
    }

    /**
     * Implementation of the Pollard's rho factorization algorithm.
     * <p>
     * This implementation follows the paper "An improved Monte Carlo factorization algorithm"
     * by Richard P. Brent. This avoids the triple computation of f(x) typically found in Pollard's
     * rho implementations. It also batches several gcd computation into 1.
     * <p>
     * The backtracking is not implemented as we deal only with semi-primes.
     *
     * @param n number to factor, must be semi-prime.
     * @return a prime factor of n.
     */
    static int rhoBrent(final int n) {
        final int x0 = 2;
        final int m = 25;
        int cst = SmallPrimes.PRIMES_LAST;
        int y = x0;
        int r = 1;
        do {
            int x = y;
            for (int i = 0; i < r; i++) {
                final long y2 = ((long) y) * y;
                y = (int) ((y2 + cst) % n);
            }
            int k = 0;
            do {
                final int bound = FastMath.min(m, r - k);
                int q = 1;
                for (int i = -3; i < bound; i++) { //start at -3 to ensure we enter this loop at least 3 times
                    final long y2 = ((long) y) * y;
                    y = (int) ((y2 + cst) % n);
                    final long divisor = FastMath.abs(x - y);
                    if (0 == divisor) {
                        cst += SmallPrimes.PRIMES_LAST;
                        k = -m;
                        y = x0;
                        r = 1;
                        break;
                    }
                    final long prod = divisor * q;
                    q = (int) (prod % n);
                    if (0 == q) {
                        return gcdPositive(FastMath.abs((int) divisor), n);
                    }
                }
                final int out = gcdPositive(FastMath.abs(q), n);
                if (1 != out) {
                    return out;
                }
                k += m;
            } while (k < r);
            r = 2 * r;
        } while (true);
    }

    /**
     * Gcd between two positive numbers.
     * <p>
     * Gets the greatest common divisor of two numbers, using the "binary gcd" method,
     * which avoids division and modulo operations. See Knuth 4.5.2 algorithm B.
     * This algorithm is due to Josef Stein (1961).
     * </p>
     * Special cases:
     * <ul>
     * <li>The result of {@code gcd(x, x)}, {@code gcd(0, x)} and {@code gcd(x, 0)} is the value of {@code x}.</li>
     * <li>The invocation {@code gcd(0, 0)} is the only one which returns {@code 0}.</li>
     * </ul>
     *
     * @param a first number, must be &ge; 0
     * @param b second number, must be &ge; 0
     * @return gcd(a,b)
     */
    static int gcdPositive(int a, int b){
        // both a and b must be positive, it is not checked here
        // gdc(a,0) = a
        if (a == 0) {
            return b;
        } else if (b == 0) {
            return a;
        }

        // make a and b odd, keep in mind the common power of twos
        final int aTwos = Integer.numberOfTrailingZeros(a);
        a >>= aTwos;
        final int bTwos = Integer.numberOfTrailingZeros(b);
        b >>= bTwos;
        final int shift = FastMath.min(aTwos, bTwos);

        // a and b >0
        // if a > b then gdc(a,b) = gcd(a-b,b)
        // if a < b then gcd(a,b) = gcd(b-a,a)
        // so next a is the absolute difference and next b is the minimum of current values
        while (a != b) {
            final int delta = a - b;
            b = FastMath.min(a, b);
            a = FastMath.abs(delta);
            // for speed optimization:
            // remove any power of two in a as b is guaranteed to be odd throughout all iterations
            a >>= Integer.numberOfTrailingZeros(a);
        }

        // gcd(a,a) = a, just "add" the common power of twos
        return a << shift;
    }
}
