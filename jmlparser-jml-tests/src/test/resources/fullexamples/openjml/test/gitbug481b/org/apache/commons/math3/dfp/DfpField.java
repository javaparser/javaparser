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

import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;

/** Field for Decimal floating point instances.
 * @since 2.2
 */
public class DfpField implements Field<Dfp> {

    /** Enumerate for rounding modes. */
    public enum RoundingMode {

        /** Rounds toward zero (truncation). */
        ROUND_DOWN,

        /** Rounds away from zero if discarded digit is non-zero. */
        ROUND_UP,

        /** Rounds towards nearest unless both are equidistant in which case it rounds away from zero. */
        ROUND_HALF_UP,

        /** Rounds towards nearest unless both are equidistant in which case it rounds toward zero. */
        ROUND_HALF_DOWN,

        /** Rounds towards nearest unless both are equidistant in which case it rounds toward the even neighbor.
         * This is the default as  specified by IEEE 854-1987
         */
        ROUND_HALF_EVEN,

        /** Rounds towards nearest unless both are equidistant in which case it rounds toward the odd neighbor.  */
        ROUND_HALF_ODD,

        /** Rounds towards positive infinity. */
        ROUND_CEIL,

        /** Rounds towards negative infinity. */
        ROUND_FLOOR;

    }

    /** IEEE 854-1987 flag for invalid operation. */
    public static final int FLAG_INVALID   =  1;

    /** IEEE 854-1987 flag for division by zero. */
    public static final int FLAG_DIV_ZERO  =  2;

    /** IEEE 854-1987 flag for overflow. */
    public static final int FLAG_OVERFLOW  =  4;

    /** IEEE 854-1987 flag for underflow. */
    public static final int FLAG_UNDERFLOW =  8;

    /** IEEE 854-1987 flag for inexact result. */
    public static final int FLAG_INEXACT   = 16;

    /** High precision string representation of &radic;2. */
    private static String sqr2String;

    // Note: the static strings are set up (once) by the ctor and @GuardedBy("DfpField.class")

    /** High precision string representation of &radic;2 / 2. */
    private static String sqr2ReciprocalString;

    /** High precision string representation of &radic;3. */
    private static String sqr3String;

    /** High precision string representation of &radic;3 / 3. */
    private static String sqr3ReciprocalString;

    /** High precision string representation of &pi;. */
    private static String piString;

    /** High precision string representation of e. */
    private static String eString;

    /** High precision string representation of ln(2). */
    private static String ln2String;

    /** High precision string representation of ln(5). */
    private static String ln5String;

    /** High precision string representation of ln(10). */
    private static String ln10String;

    /** The number of radix digits.
     * Note these depend on the radix which is 10000 digits,
     * so each one is equivalent to 4 decimal digits.
     */
    private final int radixDigits;

    /** A {@link Dfp} with value 0. */
    private final Dfp zero;

    /** A {@link Dfp} with value 1. */
    private final Dfp one;

    /** A {@link Dfp} with value 2. */
    private final Dfp two;

    /** A {@link Dfp} with value &radic;2. */
    private final Dfp sqr2;

    /** A two elements {@link Dfp} array with value &radic;2 split in two pieces. */
    private final Dfp[] sqr2Split;

    /** A {@link Dfp} with value &radic;2 / 2. */
    private final Dfp sqr2Reciprocal;

    /** A {@link Dfp} with value &radic;3. */
    private final Dfp sqr3;

    /** A {@link Dfp} with value &radic;3 / 3. */
    private final Dfp sqr3Reciprocal;

    /** A {@link Dfp} with value &pi;. */
    private final Dfp pi;

    /** A two elements {@link Dfp} array with value &pi; split in two pieces. */
    private final Dfp[] piSplit;

    /** A {@link Dfp} with value e. */
    private final Dfp e;

    /** A two elements {@link Dfp} array with value e split in two pieces. */
    private final Dfp[] eSplit;

    /** A {@link Dfp} with value ln(2). */
    private final Dfp ln2;

    /** A two elements {@link Dfp} array with value ln(2) split in two pieces. */
    private final Dfp[] ln2Split;

    /** A {@link Dfp} with value ln(5). */
    private final Dfp ln5;

    /** A two elements {@link Dfp} array with value ln(5) split in two pieces. */
    private final Dfp[] ln5Split;

    /** A {@link Dfp} with value ln(10). */
    private final Dfp ln10;

    /** Current rounding mode. */
    private RoundingMode rMode;

    /** IEEE 854-1987 signals. */
    private int ieeeFlags;

    /** Create a factory for the specified number of radix digits.
     * <p>
     * Note that since the {@link Dfp} class uses 10000 as its radix, each radix
     * digit is equivalent to 4 decimal digits. This implies that asking for
     * 13, 14, 15 or 16 decimal digits will really lead to a 4 radix 10000 digits in
     * all cases.
     * </p>
     * @param decimalDigits minimal number of decimal digits.
     */
    public DfpField(final int decimalDigits) {
        this(decimalDigits, true);
    }

    /** Create a factory for the specified number of radix digits.
     * <p>
     * Note that since the {@link Dfp} class uses 10000 as its radix, each radix
     * digit is equivalent to 4 decimal digits. This implies that asking for
     * 13, 14, 15 or 16 decimal digits will really lead to a 4 radix 10000 digits in
     * all cases.
     * </p>
     * @param decimalDigits minimal number of decimal digits
     * @param computeConstants if true, the transcendental constants for the given precision
     * must be computed (setting this flag to false is RESERVED for the internal recursive call)
     */
    private DfpField(final int decimalDigits, final boolean computeConstants) {

        this.radixDigits = (decimalDigits < 13) ? 4 : (decimalDigits + 3) / 4;
        this.rMode       = RoundingMode.ROUND_HALF_EVEN;
        this.ieeeFlags   = 0;
        this.zero        = new Dfp(this, 0);
        this.one         = new Dfp(this, 1);
        this.two         = new Dfp(this, 2);

        if (computeConstants) {
            // set up transcendental constants
            synchronized (DfpField.class) {

                // as a heuristic to circumvent Table-Maker's Dilemma, we set the string
                // representation of the constants to be at least 3 times larger than the
                // number of decimal digits, also as an attempt to really compute these
                // constants only once, we set a minimum number of digits
                computeStringConstants((decimalDigits < 67) ? 200 : (3 * decimalDigits));

                // set up the constants at current field accuracy
                sqr2           = new Dfp(this, sqr2String);
                sqr2Split      = split(sqr2String);
                sqr2Reciprocal = new Dfp(this, sqr2ReciprocalString);
                sqr3           = new Dfp(this, sqr3String);
                sqr3Reciprocal = new Dfp(this, sqr3ReciprocalString);
                pi             = new Dfp(this, piString);
                piSplit        = split(piString);
                e              = new Dfp(this, eString);
                eSplit         = split(eString);
                ln2            = new Dfp(this, ln2String);
                ln2Split       = split(ln2String);
                ln5            = new Dfp(this, ln5String);
                ln5Split       = split(ln5String);
                ln10           = new Dfp(this, ln10String);

            }
        } else {
            // dummy settings for unused constants
            sqr2           = null;
            sqr2Split      = null;
            sqr2Reciprocal = null;
            sqr3           = null;
            sqr3Reciprocal = null;
            pi             = null;
            piSplit        = null;
            e              = null;
            eSplit         = null;
            ln2            = null;
            ln2Split       = null;
            ln5            = null;
            ln5Split       = null;
            ln10           = null;
        }

    }

    /** Get the number of radix digits of the {@link Dfp} instances built by this factory.
     * @return number of radix digits
     */
    public int getRadixDigits() {
        return radixDigits;
    }

    /** Set the rounding mode.
     *  If not set, the default value is {@link RoundingMode#ROUND_HALF_EVEN}.
     * @param mode desired rounding mode
     * Note that the rounding mode is common to all {@link Dfp} instances
     * belonging to the current {@link DfpField} in the system and will
     * affect all future calculations.
     */
    public void setRoundingMode(final RoundingMode mode) {
        rMode = mode;
    }

    /** Get the current rounding mode.
     * @return current rounding mode
     */
    public RoundingMode getRoundingMode() {
        return rMode;
    }

    /** Get the IEEE 854 status flags.
     * @return IEEE 854 status flags
     * @see #clearIEEEFlags()
     * @see #setIEEEFlags(int)
     * @see #setIEEEFlagsBits(int)
     * @see #FLAG_INVALID
     * @see #FLAG_DIV_ZERO
     * @see #FLAG_OVERFLOW
     * @see #FLAG_UNDERFLOW
     * @see #FLAG_INEXACT
     */
    public int getIEEEFlags() {
        return ieeeFlags;
    }

    /** Clears the IEEE 854 status flags.
     * @see #getIEEEFlags()
     * @see #setIEEEFlags(int)
     * @see #setIEEEFlagsBits(int)
     * @see #FLAG_INVALID
     * @see #FLAG_DIV_ZERO
     * @see #FLAG_OVERFLOW
     * @see #FLAG_UNDERFLOW
     * @see #FLAG_INEXACT
     */
    public void clearIEEEFlags() {
        ieeeFlags = 0;
    }

    /** Sets the IEEE 854 status flags.
     * @param flags desired value for the flags
     * @see #getIEEEFlags()
     * @see #clearIEEEFlags()
     * @see #setIEEEFlagsBits(int)
     * @see #FLAG_INVALID
     * @see #FLAG_DIV_ZERO
     * @see #FLAG_OVERFLOW
     * @see #FLAG_UNDERFLOW
     * @see #FLAG_INEXACT
     */
    public void setIEEEFlags(final int flags) {
        ieeeFlags = flags & (FLAG_INVALID | FLAG_DIV_ZERO | FLAG_OVERFLOW | FLAG_UNDERFLOW | FLAG_INEXACT);
    }

    /** Sets some bits in the IEEE 854 status flags, without changing the already set bits.
     * <p>
     * Calling this method is equivalent to call {@code setIEEEFlags(getIEEEFlags() | bits)}
     * </p>
     * @param bits bits to set
     * @see #getIEEEFlags()
     * @see #clearIEEEFlags()
     * @see #setIEEEFlags(int)
     * @see #FLAG_INVALID
     * @see #FLAG_DIV_ZERO
     * @see #FLAG_OVERFLOW
     * @see #FLAG_UNDERFLOW
     * @see #FLAG_INEXACT
     */
    public void setIEEEFlagsBits(final int bits) {
        ieeeFlags |= bits & (FLAG_INVALID | FLAG_DIV_ZERO | FLAG_OVERFLOW | FLAG_UNDERFLOW | FLAG_INEXACT);
    }

    /** Makes a {@link Dfp} with a value of 0.
     * @return a new {@link Dfp} with a value of 0
     */
    public Dfp newDfp() {
        return new Dfp(this);
    }

    /** Create an instance from a byte value.
     * @param x value to convert to an instance
     * @return a new {@link Dfp} with the same value as x
     */
    public Dfp newDfp(final byte x) {
        return new Dfp(this, x);
    }

    /** Create an instance from an int value.
     * @param x value to convert to an instance
     * @return a new {@link Dfp} with the same value as x
     */
    public Dfp newDfp(final int x) {
        return new Dfp(this, x);
    }

    /** Create an instance from a long value.
     * @param x value to convert to an instance
     * @return a new {@link Dfp} with the same value as x
     */
    public Dfp newDfp(final long x) {
        return new Dfp(this, x);
    }

    /** Create an instance from a double value.
     * @param x value to convert to an instance
     * @return a new {@link Dfp} with the same value as x
     */
    public Dfp newDfp(final double x) {
        return new Dfp(this, x);
    }

    /** Copy constructor.
     * @param d instance to copy
     * @return a new {@link Dfp} with the same value as d
     */
    public Dfp newDfp(Dfp d) {
        return new Dfp(d);
    }

    /** Create a {@link Dfp} given a String representation.
     * @param s string representation of the instance
     * @return a new {@link Dfp} parsed from specified string
     */
    public Dfp newDfp(final String s) {
        return new Dfp(this, s);
    }

    /** Creates a {@link Dfp} with a non-finite value.
     * @param sign sign of the Dfp to create
     * @param nans code of the value, must be one of {@link Dfp#INFINITE},
     * {@link Dfp#SNAN},  {@link Dfp#QNAN}
     * @return a new {@link Dfp} with a non-finite value
     */
    public Dfp newDfp(final byte sign, final byte nans) {
        return new Dfp(this, sign, nans);
    }

    /** Get the constant 0.
     * @return a {@link Dfp} with value 0
     */
    public Dfp getZero() {
        return zero;
    }

    /** Get the constant 1.
     * @return a {@link Dfp} with value 1
     */
    public Dfp getOne() {
        return one;
    }

    /** {@inheritDoc} */
    public Class<? extends FieldElement<Dfp>> getRuntimeClass() {
        return Dfp.class;
    }

    /** Get the constant 2.
     * @return a {@link Dfp} with value 2
     */
    public Dfp getTwo() {
        return two;
    }

    /** Get the constant &radic;2.
     * @return a {@link Dfp} with value &radic;2
     */
    public Dfp getSqr2() {
        return sqr2;
    }

    /** Get the constant &radic;2 split in two pieces.
     * @return a {@link Dfp} with value &radic;2 split in two pieces
     */
    public Dfp[] getSqr2Split() {
        return sqr2Split.clone();
    }

    /** Get the constant &radic;2 / 2.
     * @return a {@link Dfp} with value &radic;2 / 2
     */
    public Dfp getSqr2Reciprocal() {
        return sqr2Reciprocal;
    }

    /** Get the constant &radic;3.
     * @return a {@link Dfp} with value &radic;3
     */
    public Dfp getSqr3() {
        return sqr3;
    }

    /** Get the constant &radic;3 / 3.
     * @return a {@link Dfp} with value &radic;3 / 3
     */
    public Dfp getSqr3Reciprocal() {
        return sqr3Reciprocal;
    }

    /** Get the constant &pi;.
     * @return a {@link Dfp} with value &pi;
     */
    public Dfp getPi() {
        return pi;
    }

    /** Get the constant &pi; split in two pieces.
     * @return a {@link Dfp} with value &pi; split in two pieces
     */
    public Dfp[] getPiSplit() {
        return piSplit.clone();
    }

    /** Get the constant e.
     * @return a {@link Dfp} with value e
     */
    public Dfp getE() {
        return e;
    }

    /** Get the constant e split in two pieces.
     * @return a {@link Dfp} with value e split in two pieces
     */
    public Dfp[] getESplit() {
        return eSplit.clone();
    }

    /** Get the constant ln(2).
     * @return a {@link Dfp} with value ln(2)
     */
    public Dfp getLn2() {
        return ln2;
    }

    /** Get the constant ln(2) split in two pieces.
     * @return a {@link Dfp} with value ln(2) split in two pieces
     */
    public Dfp[] getLn2Split() {
        return ln2Split.clone();
    }

    /** Get the constant ln(5).
     * @return a {@link Dfp} with value ln(5)
     */
    public Dfp getLn5() {
        return ln5;
    }

    /** Get the constant ln(5) split in two pieces.
     * @return a {@link Dfp} with value ln(5) split in two pieces
     */
    public Dfp[] getLn5Split() {
        return ln5Split.clone();
    }

    /** Get the constant ln(10).
     * @return a {@link Dfp} with value ln(10)
     */
    public Dfp getLn10() {
        return ln10;
    }

    /** Breaks a string representation up into two {@link Dfp}'s.
     * The split is such that the sum of them is equivalent to the input string,
     * but has higher precision than using a single Dfp.
     * @param a string representation of the number to split
     * @return an array of two {@link Dfp Dfp} instances which sum equals a
     */
    private Dfp[] split(final String a) {
      Dfp result[] = new Dfp[2];
      boolean leading = true;
      int sp = 0;
      int sig = 0;

      char[] buf = new char[a.length()];

      for (int i = 0; i < buf.length; i++) {
        buf[i] = a.charAt(i);

        if (buf[i] >= '1' && buf[i] <= '9') {
            leading = false;
        }

        if (buf[i] == '.') {
          sig += (400 - sig) % 4;
          leading = false;
        }

        if (sig == (radixDigits / 2) * 4) {
          sp = i;
          break;
        }

        if (buf[i] >= '0' && buf[i] <= '9' && !leading) {
            sig ++;
        }
      }

      result[0] = new Dfp(this, new String(buf, 0, sp));

      for (int i = 0; i < buf.length; i++) {
        buf[i] = a.charAt(i);
        if (buf[i] >= '0' && buf[i] <= '9' && i < sp) {
            buf[i] = '0';
        }
      }

      result[1] = new Dfp(this, new String(buf));

      return result;

    }

    /** Recompute the high precision string constants.
     * @param highPrecisionDecimalDigits precision at which the string constants mus be computed
     */
    private static void computeStringConstants(final int highPrecisionDecimalDigits) {
        if (sqr2String == null || sqr2String.length() < highPrecisionDecimalDigits - 3) {

            // recompute the string representation of the transcendental constants
            final DfpField highPrecisionField = new DfpField(highPrecisionDecimalDigits, false);
            final Dfp highPrecisionOne        = new Dfp(highPrecisionField, 1);
            final Dfp highPrecisionTwo        = new Dfp(highPrecisionField, 2);
            final Dfp highPrecisionThree      = new Dfp(highPrecisionField, 3);

            final Dfp highPrecisionSqr2 = highPrecisionTwo.sqrt();
            sqr2String           = highPrecisionSqr2.toString();
            sqr2ReciprocalString = highPrecisionOne.divide(highPrecisionSqr2).toString();

            final Dfp highPrecisionSqr3 = highPrecisionThree.sqrt();
            sqr3String           = highPrecisionSqr3.toString();
            sqr3ReciprocalString = highPrecisionOne.divide(highPrecisionSqr3).toString();

            piString   = computePi(highPrecisionOne, highPrecisionTwo, highPrecisionThree).toString();
            eString    = computeExp(highPrecisionOne, highPrecisionOne).toString();
            ln2String  = computeLn(highPrecisionTwo, highPrecisionOne, highPrecisionTwo).toString();
            ln5String  = computeLn(new Dfp(highPrecisionField, 5),  highPrecisionOne, highPrecisionTwo).toString();
            ln10String = computeLn(new Dfp(highPrecisionField, 10), highPrecisionOne, highPrecisionTwo).toString();

        }
    }

    /** Compute &pi; using Jonathan and Peter Borwein quartic formula.
     * @param one constant with value 1 at desired precision
     * @param two constant with value 2 at desired precision
     * @param three constant with value 3 at desired precision
     * @return &pi;
     */
    private static Dfp computePi(final Dfp one, final Dfp two, final Dfp three) {

        Dfp sqrt2   = two.sqrt();
        Dfp yk      = sqrt2.subtract(one);
        Dfp four    = two.add(two);
        Dfp two2kp3 = two;
        Dfp ak      = two.multiply(three.subtract(two.multiply(sqrt2)));

        // The formula converges quartically. This means the number of correct
        // digits is multiplied by 4 at each iteration! Five iterations are
        // sufficient for about 160 digits, eight iterations give about
        // 10000 digits (this has been checked) and 20 iterations more than
        // 160 billions of digits (this has NOT been checked).
        // So the limit here is considered sufficient for most purposes ...
        for (int i = 1; i < 20; i++) {
            final Dfp ykM1 = yk;

            final Dfp y2         = yk.multiply(yk);
            final Dfp oneMinusY4 = one.subtract(y2.multiply(y2));
            final Dfp s          = oneMinusY4.sqrt().sqrt();
            yk = one.subtract(s).divide(one.add(s));

            two2kp3 = two2kp3.multiply(four);

            final Dfp p = one.add(yk);
            final Dfp p2 = p.multiply(p);
            ak = ak.multiply(p2.multiply(p2)).subtract(two2kp3.multiply(yk).multiply(one.add(yk).add(yk.multiply(yk))));

            if (yk.equals(ykM1)) {
                break;
            }
        }

        return one.divide(ak);

    }

    /** Compute exp(a).
     * @param a number for which we want the exponential
     * @param one constant with value 1 at desired precision
     * @return exp(a)
     */
    public static Dfp computeExp(final Dfp a, final Dfp one) {

        Dfp y  = new Dfp(one);
        Dfp py = new Dfp(one);
        Dfp f  = new Dfp(one);
        Dfp fi = new Dfp(one);
        Dfp x  = new Dfp(one);

        for (int i = 0; i < 10000; i++) {
            x = x.multiply(a);
            y = y.add(x.divide(f));
            fi = fi.add(one);
            f = f.multiply(fi);
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y;

    }


    /** Compute ln(a).
     *
     *  Let f(x) = ln(x),
     *
     *  We know that f'(x) = 1/x, thus from Taylor's theorem we have:
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
     * @param a number for which we want the exponential
     * @param one constant with value 1 at desired precision
     * @param two constant with value 2 at desired precision
     * @return ln(a)
     */

    public static Dfp computeLn(final Dfp a, final Dfp one, final Dfp two) {

        int den = 1;
        Dfp x = a.add(new Dfp(a.getField(), -1)).divide(a.add(one));

        Dfp y = new Dfp(x);
        Dfp num = new Dfp(x);
        Dfp py = new Dfp(y);
        for (int i = 0; i < 10000; i++) {
            num = num.multiply(x);
            num = num.multiply(x);
            den += 2;
            Dfp t = num.divide(den);
            y = y.add(t);
            if (y.equals(py)) {
                break;
            }
            py = new Dfp(y);
        }

        return y.multiply(two);

    }

}
