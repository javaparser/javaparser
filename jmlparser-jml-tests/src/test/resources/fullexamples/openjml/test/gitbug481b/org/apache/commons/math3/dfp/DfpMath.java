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

package org.apache.commons.math3.dfp;

/** Mathematical routines for use with {@link Dfp}.
 * The constants are defined in {@link DfpField}
 * @since 2.2
 */
public class DfpMath {

    /** Name for traps triggered by pow. */
    private static final String POW_TRAP = "pow";

    /**
     * Private Constructor.
     */
    private DfpMath() {
    }

    /** Breaks a string representation up into two dfp's.
     * <p>The two dfp are such that the sum of them is equivalent
     * to the input string, but has higher precision than using a
     * single dfp. This is useful for improving accuracy of
     * exponentiation and critical multiplies.
     * @param field field to which the Dfp must belong
     * @param a string representation to split
     * @return an array of two {@link Dfp} which sum is a
     */
    protected static Dfp[] split(final DfpField field, final String a) {
        Dfp result[] = new Dfp[2];
        char[] buf;
        boolean leading = true;
        int sp = 0;
        int sig = 0;

        buf = new char[a.length()];

        for (int i = 0; i < buf.length; i++) {
            buf[i] = a.charAt(i);

            if (buf[i] >= '1' && buf[i] <= '9') {
                leading = false;
            }

            if (buf[i] == '.') {
                sig += (400 - sig) % 4;
                leading = false;
            }

            if (sig == (field.getRadixDigits() / 2) * 4) {
                sp = i;
                break;
            }

            if (buf[i] >= '0' && buf[i] <= '9' && !leading) {
                sig ++;
            }
        }

        result[0] = field.newDfp(new String(buf, 0, sp));

        for (int i = 0; i < buf.length; i++) {
            buf[i] = a.charAt(i);
            if (buf[i] >= '0' && buf[i] <= '9' && i < sp) {
                buf[i] = '0';
            }
        }

        result[1] = field.newDfp(new String(buf));

        return result;
    }

    /** Splits a {@link Dfp} into 2 {@link Dfp}'s such that their sum is equal to the input {@link Dfp}.
     * @param a number to split
     * @return two elements array containing the split number
     */
    protected static Dfp[] split(final Dfp a) {
        final Dfp[] result = new Dfp[2];
        final Dfp shift = a.multiply(a.power10K(a.getRadixDigits() / 2));
        result[0] = a.add(shift).subtract(shift);
        result[1] = a.subtract(result[0]);
        return result;
    }

    /** Multiply two numbers that are split in to two pieces that are
     *  meant to be added together.
     *  Use binomial multiplication so ab = a0 b0 + a0 b1 + a1 b0 + a1 b1
     *  Store the first term in result0, the rest in result1
     *  @param a first factor of the multiplication, in split form
     *  @param b second factor of the multiplication, in split form
     *  @return a &times; b, in split form
     */
    protected static Dfp[] splitMult(final Dfp[] a, final Dfp[] b) {
        final Dfp[] result = new Dfp[2];

        result[1] = a[0].getZero();
        result[0] = a[0].multiply(b[0]);

        /* If result[0] is infinite or zero, don't compute result[1].
         * Attempting to do so may produce NaNs.
         */

        if (result[0].classify() == Dfp.INFINITE || result[0].equals(result[1])) {
            return result;
        }

        result[1] = a[0].multiply(b[1]).add(a[1].multiply(b[0])).add(a[1].multiply(b[1]));

        return result;
    }

    /** Divide two numbers that are split in to two pieces that are meant to be added together.
     * Inverse of split multiply above:
     *  (a+b) / (c+d) = (a/c) + ( (bc-ad)/(c**2+cd) )
     *  @param a dividend, in split form
     *  @param b divisor, in split form
     *  @return a / b, in split form
     */
    protected static Dfp[] splitDiv(final Dfp[] a, final Dfp[] b) {
        final Dfp[] result;

        result = new Dfp[2];

        result[0] = a[0].divide(b[0]);
        result[1] = a[1].multiply(b[0]).subtract(a[0].multiply(b[1]));
        result[1] = result[1].divide(b[0].multiply(b[0]).add(b[0].multiply(b[1])));

        return result;
    }

    /** Raise a split base to the a power.
     * @param base number to raise
     * @param a power
     * @return base<sup>a</sup>
     */
    protected static Dfp splitPow(final Dfp[] base, int a) {
        boolean invert = false;

        Dfp[] r = new Dfp[2];

        Dfp[] result = new Dfp[2];
        result[0] = base[0].getOne();
        result[1] = base[0].getZero();

        if (a == 0) {
            // Special case a = 0
            return result[0].add(result[1]);
        }

        if (a < 0) {
            // If a is less than zero
            invert = true;
            a = -a;
        }

        // Exponentiate by successive squaring
        do {
            r[0] = new Dfp(base[0]);
            r[1] = new Dfp(base[1]);
            int trial = 1;

            int prevtrial;
            while (true) {
                prevtrial = trial;
                trial *= 2;
                if (trial > a) {
                    break;
                }
                r = splitMult(r, r);
            }

            trial = prevtrial;

            a -= trial;
            result = splitMult(result, r);

        } while (a >= 1);

        result[0] = result[0].add(result[1]);

        if (invert) {
            result[0] = base[0].getOne().divide(result[0]);
        }

        return result[0];

    }

    /** Raises base to the power a by successive squaring.
     * @param base number to raise
     * @param a power
     * @return base<sup>a</sup>
     */
    public static Dfp pow(Dfp base, int a)
    {
        boolean invert = false;

        Dfp result = base.getOne();

        if (a == 0) {
            // Special case
            return result;
        }

        if (a < 0) {
            invert = true;
            a = -a;
        }

        // Exponentiate by successive squaring
        do {
            Dfp r = new Dfp(base);
            Dfp prevr;
            int trial = 1;
            int prevtrial;

            do {
                prevr = new Dfp(r);
                prevtrial = trial;
                r = r.multiply(r);
                trial *= 2;
            } while (a>trial);

            r = prevr;
            trial = prevtrial;

            a -= trial;
            result = result.multiply(r);

        } while (a >= 1);

        if (invert) {
            result = base.getOne().divide(result);
        }

        return base.newInstance(result);

    }

    /** Computes e to the given power.
     * a is broken into two parts, such that a = n+m  where n is an integer.
     * We use pow() to compute e<sup>n</sup> and a Taylor series to compute
     * e<sup>m</sup>.  We return e*<sup>n</sup> &times; e<sup>m</sup>
     * @param a power at which e should be raised
     * @return e<sup>a</sup>
     */
    public static Dfp exp(final Dfp a) {

        final Dfp inta = a.rint();
        final Dfp fraca = a.subtract(inta);

        final int ia = inta.intValue();
        if (ia > 2147483646) {
            // return +Infinity
            return a.newInstance((byte)1, Dfp.INFINITE);
        }

        if (ia < -2147483646) {
            // return 0;
            return a.newInstance();
        }

        final Dfp einta = splitPow(a.getField().getESplit(), ia);
        final Dfp efraca = expInternal(fraca);

        return einta.multiply(efraca);
    }

    /** Computes e to the given power.
     * Where -1 < a < 1.  Use the classic Taylor series.  1 + x**2/2! + x**3/3! + x**4/4!  ...
     * @param a power at which e should be raised
     * @return e<sup>a</sup>
     */
    protected static Dfp expInternal(final Dfp a) {
        Dfp y = a.getOne();
        Dfp x = a.getOne();
        Dfp fact = a.getOne();
        Dfp py = new Dfp(y);

        for (int i = 1; i < 90; i++) {
            x = x.multiply(a);
            fact = fact.divide(i);
            y = y.add(x.multiply(fact));
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y;
    }

    /** Returns the natural logarithm of a.
     * a is first split into three parts such that  a = (10000^h)(2^j)k.
     * ln(a) is computed by ln(a) = ln(5)*h + ln(2)*(h+j) + ln(k)
     * k is in the range 2/3 < k <4/3 and is passed on to a series expansion.
     * @param a number from which logarithm is requested
     * @return log(a)
     */
    public static Dfp log(Dfp a) {
        int lr;
        Dfp x;
        int ix;
        int p2 = 0;

        // Check the arguments somewhat here
        if (a.equals(a.getZero()) || a.lessThan(a.getZero()) || a.isNaN()) {
            // negative, zero or NaN
            a.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            return a.dotrap(DfpField.FLAG_INVALID, "ln", a, a.newInstance((byte)1, Dfp.QNAN));
        }

        if (a.classify() == Dfp.INFINITE) {
            return a;
        }

        x = new Dfp(a);
        lr = x.log10K();

        x = x.divide(pow(a.newInstance(10000), lr));  /* This puts x in the range 0-10000 */
        ix = x.floor().intValue();

        while (ix > 2) {
            ix >>= 1;
            p2++;
        }


        Dfp[] spx = split(x);
        Dfp[] spy = new Dfp[2];
        spy[0] = pow(a.getTwo(), p2);          // use spy[0] temporarily as a divisor
        spx[0] = spx[0].divide(spy[0]);
        spx[1] = spx[1].divide(spy[0]);

        spy[0] = a.newInstance("1.33333");    // Use spy[0] for comparison
        while (spx[0].add(spx[1]).greaterThan(spy[0])) {
            spx[0] = spx[0].divide(2);
            spx[1] = spx[1].divide(2);
            p2++;
        }

        // X is now in the range of 2/3 < x < 4/3
        Dfp[] spz = logInternal(spx);

        spx[0] = a.newInstance(new StringBuilder().append(p2+4*lr).toString());
        spx[1] = a.getZero();
        spy = splitMult(a.getField().getLn2Split(), spx);

        spz[0] = spz[0].add(spy[0]);
        spz[1] = spz[1].add(spy[1]);

        spx[0] = a.newInstance(new StringBuilder().append(4*lr).toString());
        spx[1] = a.getZero();
        spy = splitMult(a.getField().getLn5Split(), spx);

        spz[0] = spz[0].add(spy[0]);
        spz[1] = spz[1].add(spy[1]);

        return a.newInstance(spz[0].add(spz[1]));

    }

    /** Computes the natural log of a number between 0 and 2.
     *  Let f(x) = ln(x),
     *
     *  We know that f'(x) = 1/x, thus from Taylor's theorum we have:
     *
     *           -----          n+1         n
     *  f(x) =   \           (-1)    (x - 1)
     *           /          ----------------    for 1 <= n <= infinity
     *           -----             n
     *
     *  or
     *                       2        3       4
     *                   (x-1)   (x-1)    (x-1)
     *  ln(x) =  (x-1) - ----- + ------ - ------ + ...
     *                     2       3        4
     *
     *  alternatively,
     *
     *                  2    3   4
     *                 x    x   x
     *  ln(x+1) =  x - -  + - - - + ...
     *                 2    3   4
     *
     *  This series can be used to compute ln(x), but it converges too slowly.
     *
     *  If we substitute -x for x above, we get
     *
     *                   2    3    4
     *                  x    x    x
     *  ln(1-x) =  -x - -  - -  - - + ...
     *                  2    3    4
     *
     *  Note that all terms are now negative.  Because the even powered ones
     *  absorbed the sign.  Now, subtract the series above from the previous
     *  one to get ln(x+1) - ln(1-x).  Note the even terms cancel out leaving
     *  only the odd ones
     *
     *                             3     5      7
     *                           2x    2x     2x
     *  ln(x+1) - ln(x-1) = 2x + --- + --- + ---- + ...
     *                            3     5      7
     *
     *  By the property of logarithms that ln(a) - ln(b) = ln (a/b) we have:
     *
     *                                3        5        7
     *      x+1           /          x        x        x          \
     *  ln ----- =   2 *  |  x  +   ----  +  ----  +  ---- + ...  |
     *      x-1           \          3        5        7          /
     *
     *  But now we want to find ln(a), so we need to find the value of x
     *  such that a = (x+1)/(x-1).   This is easily solved to find that
     *  x = (a-1)/(a+1).
     * @param a number from which logarithm is requested, in split form
     * @return log(a)
     */
    protected static Dfp[] logInternal(final Dfp a[]) {

        /* Now we want to compute x = (a-1)/(a+1) but this is prone to
         * loss of precision.  So instead, compute x = (a/4 - 1/4) / (a/4 + 1/4)
         */
        Dfp t = a[0].divide(4).add(a[1].divide(4));
        Dfp x = t.add(a[0].newInstance("-0.25")).divide(t.add(a[0].newInstance("0.25")));

        Dfp y = new Dfp(x);
        Dfp num = new Dfp(x);
        Dfp py = new Dfp(y);
        int den = 1;
        for (int i = 0; i < 10000; i++) {
            num = num.multiply(x);
            num = num.multiply(x);
            den += 2;
            t = num.divide(den);
            y = y.add(t);
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        y = y.multiply(a[0].getTwo());

        return split(y);

    }

    /** Computes x to the y power.<p>
     *
     *  Uses the following method:<p>
     *
     *  <ol>
     *  <li> Set u = rint(y), v = y-u
     *  <li> Compute a = v * ln(x)
     *  <li> Compute b = rint( a/ln(2) )
     *  <li> Compute c = a - b*ln(2)
     *  <li> x<sup>y</sup> = x<sup>u</sup>  *   2<sup>b</sup> * e<sup>c</sup>
     *  </ol>
     *  if |y| > 1e8, then we compute by exp(y*ln(x))   <p>
     *
     *  <b>Special Cases</b><p>
     *  <ul>
     *  <li>  if y is 0.0 or -0.0 then result is 1.0
     *  <li>  if y is 1.0 then result is x
     *  <li>  if y is NaN then result is NaN
     *  <li>  if x is NaN and y is not zero then result is NaN
     *  <li>  if |x| > 1.0 and y is +Infinity then result is +Infinity
     *  <li>  if |x| < 1.0 and y is -Infinity then result is +Infinity
     *  <li>  if |x| > 1.0 and y is -Infinity then result is +0
     *  <li>  if |x| < 1.0 and y is +Infinity then result is +0
     *  <li>  if |x| = 1.0 and y is +/-Infinity then result is NaN
     *  <li>  if x = +0 and y > 0 then result is +0
     *  <li>  if x = +Inf and y < 0 then result is +0
     *  <li>  if x = +0 and y < 0 then result is +Inf
     *  <li>  if x = +Inf and y > 0 then result is +Inf
     *  <li>  if x = -0 and y > 0, finite, not odd integer then result is +0
     *  <li>  if x = -0 and y < 0, finite, and odd integer then result is -Inf
     *  <li>  if x = -Inf and y > 0, finite, and odd integer then result is -Inf
     *  <li>  if x = -0 and y < 0, not finite odd integer then result is +Inf
     *  <li>  if x = -Inf and y > 0, not finite odd integer then result is +Inf
     *  <li>  if x < 0 and y > 0, finite, and odd integer then result is -(|x|<sup>y</sup>)
     *  <li>  if x < 0 and y > 0, finite, and not integer then result is NaN
     *  </ul>
     *  @param x base to be raised
     *  @param y power to which base should be raised
     *  @return x<sup>y</sup>
     */
    public static Dfp pow(Dfp x, final Dfp y) {

        // make sure we don't mix number with different precision
        if (x.getField().getRadixDigits() != y.getField().getRadixDigits()) {
            x.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            final Dfp result = x.newInstance(x.getZero());
            result.nans = Dfp.QNAN;
            return x.dotrap(DfpField.FLAG_INVALID, POW_TRAP, x, result);
        }

        final Dfp zero = x.getZero();
        final Dfp one  = x.getOne();
        final Dfp two  = x.getTwo();
        boolean invert = false;
        int ui;

        /* Check for special cases */
        if (y.equals(zero)) {
            return x.newInstance(one);
        }

        if (y.equals(one)) {
            if (x.isNaN()) {
                // Test for NaNs
                x.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
                return x.dotrap(DfpField.FLAG_INVALID, POW_TRAP, x, x);
            }
            return x;
        }

        if (x.isNaN() || y.isNaN()) {
            // Test for NaNs
            x.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            return x.dotrap(DfpField.FLAG_INVALID, POW_TRAP, x, x.newInstance((byte)1, Dfp.QNAN));
        }

        // X == 0
        if (x.equals(zero)) {
            if (Dfp.copysign(one, x).greaterThan(zero)) {
                // X == +0
                if (y.greaterThan(zero)) {
                    return x.newInstance(zero);
                } else {
                    return x.newInstance(x.newInstance((byte)1, Dfp.INFINITE));
                }
            } else {
                // X == -0
                if (y.classify() == Dfp.FINITE && y.rint().equals(y) && !y.remainder(two).equals(zero)) {
                    // If y is odd integer
                    if (y.greaterThan(zero)) {
                        return x.newInstance(zero.negate());
                    } else {
                        return x.newInstance(x.newInstance((byte)-1, Dfp.INFINITE));
                    }
                } else {
                    // Y is not odd integer
                    if (y.greaterThan(zero)) {
                        return x.newInstance(zero);
                    } else {
                        return x.newInstance(x.newInstance((byte)1, Dfp.INFINITE));
                    }
                }
            }
        }

        if (x.lessThan(zero)) {
            // Make x positive, but keep track of it
            x = x.negate();
            invert = true;
        }

        if (x.greaterThan(one) && y.classify() == Dfp.INFINITE) {
            if (y.greaterThan(zero)) {
                return y;
            } else {
                return x.newInstance(zero);
            }
        }

        if (x.lessThan(one) && y.classify() == Dfp.INFINITE) {
            if (y.greaterThan(zero)) {
                return x.newInstance(zero);
            } else {
                return x.newInstance(Dfp.copysign(y, one));
            }
        }

        if (x.equals(one) && y.classify() == Dfp.INFINITE) {
            x.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            return x.dotrap(DfpField.FLAG_INVALID, POW_TRAP, x, x.newInstance((byte)1, Dfp.QNAN));
        }

        if (x.classify() == Dfp.INFINITE) {
            // x = +/- inf
            if (invert) {
                // negative infinity
                if (y.classify() == Dfp.FINITE && y.rint().equals(y) && !y.remainder(two).equals(zero)) {
                    // If y is odd integer
                    if (y.greaterThan(zero)) {
                        return x.newInstance(x.newInstance((byte)-1, Dfp.INFINITE));
                    } else {
                        return x.newInstance(zero.negate());
                    }
                } else {
                    // Y is not odd integer
                    if (y.greaterThan(zero)) {
                        return x.newInstance(x.newInstance((byte)1, Dfp.INFINITE));
                    } else {
                        return x.newInstance(zero);
                    }
                }
            } else {
                // positive infinity
                if (y.greaterThan(zero)) {
                    return x;
                } else {
                    return x.newInstance(zero);
                }
            }
        }

        if (invert && !y.rint().equals(y)) {
            x.getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            return x.dotrap(DfpField.FLAG_INVALID, POW_TRAP, x, x.newInstance((byte)1, Dfp.QNAN));
        }

        // End special cases

        Dfp r;
        if (y.lessThan(x.newInstance(100000000)) && y.greaterThan(x.newInstance(-100000000))) {
            final Dfp u = y.rint();
            ui = u.intValue();

            final Dfp v = y.subtract(u);

            if (v.unequal(zero)) {
                final Dfp a = v.multiply(log(x));
                final Dfp b = a.divide(x.getField().getLn2()).rint();

                final Dfp c = a.subtract(b.multiply(x.getField().getLn2()));
                r = splitPow(split(x), ui);
                r = r.multiply(pow(two, b.intValue()));
                r = r.multiply(exp(c));
            } else {
                r = splitPow(split(x), ui);
            }
        } else {
            // very large exponent.  |y| > 1e8
            r = exp(log(x).multiply(y));
        }

        if (invert && y.rint().equals(y) && !y.remainder(two).equals(zero)) {
            // if y is odd integer
            r = r.negate();
        }

        return x.newInstance(r);

    }

    /** Computes sin(a)  Used when 0 < a < pi/4.
     * Uses the classic Taylor series.  x - x**3/3! + x**5/5!  ...
     * @param a number from which sine is desired, in split form
     * @return sin(a)
     */
    protected static Dfp sinInternal(Dfp a[]) {

        Dfp c = a[0].add(a[1]);
        Dfp y = c;
        c = c.multiply(c);
        Dfp x = y;
        Dfp fact = a[0].getOne();
        Dfp py = new Dfp(y);

        for (int i = 3; i < 90; i += 2) {
            x = x.multiply(c);
            x = x.negate();

            fact = fact.divide((i-1)*i);  // 1 over fact
            y = y.add(x.multiply(fact));
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y;

    }

    /** Computes cos(a)  Used when 0 < a < pi/4.
     * Uses the classic Taylor series for cosine.  1 - x**2/2! + x**4/4!  ...
     * @param a number from which cosine is desired, in split form
     * @return cos(a)
     */
    protected static Dfp cosInternal(Dfp a[]) {
        final Dfp one = a[0].getOne();


        Dfp x = one;
        Dfp y = one;
        Dfp c = a[0].add(a[1]);
        c = c.multiply(c);

        Dfp fact = one;
        Dfp py = new Dfp(y);

        for (int i = 2; i < 90; i += 2) {
            x = x.multiply(c);
            x = x.negate();

            fact = fact.divide((i - 1) * i);  // 1 over fact

            y = y.add(x.multiply(fact));
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y;

    }

    /** computes the sine of the argument.
     * @param a number from which sine is desired
     * @return sin(a)
     */
    public static Dfp sin(final Dfp a) {
        final Dfp pi = a.getField().getPi();
        final Dfp zero = a.getField().getZero();
        boolean neg = false;

        /* First reduce the argument to the range of +/- PI */
        Dfp x = a.remainder(pi.multiply(2));

        /* if x < 0 then apply identity sin(-x) = -sin(x) */
        /* This puts x in the range 0 < x < PI            */
        if (x.lessThan(zero)) {
            x = x.negate();
            neg = true;
        }

        /* Since sine(x) = sine(pi - x) we can reduce the range to
         * 0 < x < pi/2
         */

        if (x.greaterThan(pi.divide(2))) {
            x = pi.subtract(x);
        }

        Dfp y;
        if (x.lessThan(pi.divide(4))) {
            y = sinInternal(split(x));
        } else {
            final Dfp c[] = new Dfp[2];
            final Dfp[] piSplit = a.getField().getPiSplit();
            c[0] = piSplit[0].divide(2).subtract(x);
            c[1] = piSplit[1].divide(2);
            y = cosInternal(c);
        }

        if (neg) {
            y = y.negate();
        }

        return a.newInstance(y);

    }

    /** computes the cosine of the argument.
     * @param a number from which cosine is desired
     * @return cos(a)
     */
    public static Dfp cos(Dfp a) {
        final Dfp pi = a.getField().getPi();
        final Dfp zero = a.getField().getZero();
        boolean neg = false;

        /* First reduce the argument to the range of +/- PI */
        Dfp x = a.remainder(pi.multiply(2));

        /* if x < 0 then apply identity cos(-x) = cos(x) */
        /* This puts x in the range 0 < x < PI           */
        if (x.lessThan(zero)) {
            x = x.negate();
        }

        /* Since cos(x) = -cos(pi - x) we can reduce the range to
         * 0 < x < pi/2
         */

        if (x.greaterThan(pi.divide(2))) {
            x = pi.subtract(x);
            neg = true;
        }

        Dfp y;
        if (x.lessThan(pi.divide(4))) {
            Dfp c[] = new Dfp[2];
            c[0] = x;
            c[1] = zero;

            y = cosInternal(c);
        } else {
            final Dfp c[] = new Dfp[2];
            final Dfp[] piSplit = a.getField().getPiSplit();
            c[0] = piSplit[0].divide(2).subtract(x);
            c[1] = piSplit[1].divide(2);
            y = sinInternal(c);
        }

        if (neg) {
            y = y.negate();
        }

        return a.newInstance(y);

    }

    /** computes the tangent of the argument.
     * @param a number from which tangent is desired
     * @return tan(a)
     */
    public static Dfp tan(final Dfp a) {
        return sin(a).divide(cos(a));
    }

    /** computes the arc-tangent of the argument.
     * @param a number from which arc-tangent is desired
     * @return atan(a)
     */
    protected static Dfp atanInternal(final Dfp a) {

        Dfp y = new Dfp(a);
        Dfp x = new Dfp(y);
        Dfp py = new Dfp(y);

        for (int i = 3; i < 90; i += 2) {
            x = x.multiply(a);
            x = x.multiply(a);
            x = x.negate();
            y = y.add(x.divide(i));
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y;

    }

    /** computes the arc tangent of the argument
     *
     *  Uses the typical taylor series
     *
     *  but may reduce arguments using the following identity
     * tan(x+y) = (tan(x) + tan(y)) / (1 - tan(x)*tan(y))
     *
     * since tan(PI/8) = sqrt(2)-1,
     *
     * atan(x) = atan( (x - sqrt(2) + 1) / (1+x*sqrt(2) - x) + PI/8.0
     * @param a number from which arc-tangent is desired
     * @return atan(a)
     */
    public static Dfp atan(final Dfp a) {
        final Dfp   zero      = a.getField().getZero();
        final Dfp   one       = a.getField().getOne();
        final Dfp[] sqr2Split = a.getField().getSqr2Split();
        final Dfp[] piSplit   = a.getField().getPiSplit();
        boolean recp = false;
        boolean neg = false;
        boolean sub = false;

        final Dfp ty = sqr2Split[0].subtract(one).add(sqr2Split[1]);

        Dfp x = new Dfp(a);
        if (x.lessThan(zero)) {
            neg = true;
            x = x.negate();
        }

        if (x.greaterThan(one)) {
            recp = true;
            x = one.divide(x);
        }

        if (x.greaterThan(ty)) {
            Dfp sty[] = new Dfp[2];
            sub = true;

            sty[0] = sqr2Split[0].subtract(one);
            sty[1] = sqr2Split[1];

            Dfp[] xs = split(x);

            Dfp[] ds = splitMult(xs, sty);
            ds[0] = ds[0].add(one);

            xs[0] = xs[0].subtract(sty[0]);
            xs[1] = xs[1].subtract(sty[1]);

            xs = splitDiv(xs, ds);
            x = xs[0].add(xs[1]);

            //x = x.subtract(ty).divide(dfp.one.add(x.multiply(ty)));
        }

        Dfp y = atanInternal(x);

        if (sub) {
            y = y.add(piSplit[0].divide(8)).add(piSplit[1].divide(8));
        }

        if (recp) {
            y = piSplit[0].divide(2).subtract(y).add(piSplit[1].divide(2));
        }

        if (neg) {
            y = y.negate();
        }

        return a.newInstance(y);

    }

    /** computes the arc-sine of the argument.
     * @param a number from which arc-sine is desired
     * @return asin(a)
     */
    public static Dfp asin(final Dfp a) {
        return atan(a.divide(a.getOne().subtract(a.multiply(a)).sqrt()));
    }

    /** computes the arc-cosine of the argument.
     * @param a number from which arc-cosine is desired
     * @return acos(a)
     */
    public static Dfp acos(Dfp a) {
        Dfp result;
        boolean negative = false;

        if (a.lessThan(a.getZero())) {
            negative = true;
        }

        a = Dfp.copysign(a, a.getOne());  // absolute value

        result = atan(a.getOne().subtract(a.multiply(a)).sqrt().divide(a));

        if (negative) {
            result = a.getField().getPi().subtract(result);
        }

        return a.newInstance(result);
    }

}
