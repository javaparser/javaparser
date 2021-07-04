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

/** Subclass of {@link Dfp} which hides the radix-10000 artifacts of the superclass.
 * This should give outward appearances of being a decimal number with DIGITS*4-3
 * decimal digits. This class can be subclassed to appear to be an arbitrary number
 * of decimal digits less than DIGITS*4-3.
 * @since 2.2
 */
public class DfpDec extends Dfp {

    /** Makes an instance with a value of zero.
     * @param factory factory linked to this instance
     */
    protected DfpDec(final DfpField factory) {
        super(factory);
    }

    /** Create an instance from a byte value.
     * @param factory factory linked to this instance
     * @param x value to convert to an instance
     */
    protected DfpDec(final DfpField factory, byte x) {
        super(factory, x);
    }

    /** Create an instance from an int value.
     * @param factory factory linked to this instance
     * @param x value to convert to an instance
     */
    protected DfpDec(final DfpField factory, int x) {
        super(factory, x);
    }

    /** Create an instance from a long value.
     * @param factory factory linked to this instance
     * @param x value to convert to an instance
     */
    protected DfpDec(final DfpField factory, long x) {
        super(factory, x);
    }

    /** Create an instance from a double value.
     * @param factory factory linked to this instance
     * @param x value to convert to an instance
     */
    protected DfpDec(final DfpField factory, double x) {
        super(factory, x);
        round(0);
    }

    /** Copy constructor.
     * @param d instance to copy
     */
    public DfpDec(final Dfp d) {
        super(d);
        round(0);
    }

    /** Create an instance from a String representation.
     * @param factory factory linked to this instance
     * @param s string representation of the instance
     */
    protected DfpDec(final DfpField factory, final String s) {
        super(factory, s);
        round(0);
    }

    /** Creates an instance with a non-finite value.
     * @param factory factory linked to this instance
     * @param sign sign of the Dfp to create
     * @param nans code of the value, must be one of {@link #INFINITE},
     * {@link #SNAN},  {@link #QNAN}
     */
    protected DfpDec(final DfpField factory, final byte sign, final byte nans) {
        super(factory, sign, nans);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance() {
        return new DfpDec(getField());
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final byte x) {
        return new DfpDec(getField(), x);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final int x) {
        return new DfpDec(getField(), x);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final long x) {
        return new DfpDec(getField(), x);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final double x) {
        return new DfpDec(getField(), x);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final Dfp d) {

        // make sure we don't mix number with different precision
        if (getField().getRadixDigits() != d.getField().getRadixDigits()) {
            getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            final Dfp result = newInstance(getZero());
            result.nans = QNAN;
            return dotrap(DfpField.FLAG_INVALID, "newInstance", d, result);
        }

        return new DfpDec(d);

    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final String s) {
        return new DfpDec(getField(), s);
    }

    /** {@inheritDoc} */
    @Override
    public Dfp newInstance(final byte sign, final byte nans) {
        return new DfpDec(getField(), sign, nans);
    }

    /** Get the number of decimal digits this class is going to represent.
     * Default implementation returns {@link #getRadixDigits()}*4-3. Subclasses can
     * override this to return something less.
     * @return number of decimal digits this class is going to represent
     */
    protected int getDecimalDigits() {
        return getRadixDigits() * 4 - 3;
    }

    /** {@inheritDoc} */
    @Override
    protected int round(int in) {

        int msb = mant[mant.length-1];
        if (msb == 0) {
            // special case -- this == zero
            return 0;
        }

        int cmaxdigits = mant.length * 4;
        int lsbthreshold = 1000;
        while (lsbthreshold > msb) {
            lsbthreshold /= 10;
            cmaxdigits --;
        }


        final int digits = getDecimalDigits();
        final int lsbshift = cmaxdigits - digits;
        final int lsd = lsbshift / 4;

        lsbthreshold = 1;
        for (int i = 0; i < lsbshift % 4; i++) {
            lsbthreshold *= 10;
        }

        final int lsb = mant[lsd];

        if (lsbthreshold <= 1 && digits == 4 * mant.length - 3) {
            return super.round(in);
        }

        int discarded = in;  // not looking at this after this point
        final int n;
        if (lsbthreshold == 1) {
            // look to the next digit for rounding
            n = (mant[lsd-1] / 1000) % 10;
            mant[lsd-1] %= 1000;
            discarded |= mant[lsd-1];
        } else {
            n = (lsb * 10 / lsbthreshold) % 10;
            discarded |= lsb % (lsbthreshold/10);
        }

        for (int i = 0; i < lsd; i++) {
            discarded |= mant[i];    // need to know if there are any discarded bits
            mant[i] = 0;
        }

        mant[lsd] = lsb / lsbthreshold * lsbthreshold;

        final boolean inc;
        switch (getField().getRoundingMode()) {
            case ROUND_DOWN:
                inc = false;
                break;

            case ROUND_UP:
                inc = (n != 0) || (discarded != 0); // round up if n!=0
                break;

            case ROUND_HALF_UP:
                inc = n >= 5;  // round half up
                break;

            case ROUND_HALF_DOWN:
                inc = n > 5;  // round half down
                break;

            case ROUND_HALF_EVEN:
                inc = (n > 5) ||
                      (n == 5 && discarded != 0) ||
                      (n == 5 && discarded == 0 && ((lsb / lsbthreshold) & 1) == 1);  // round half-even
                break;

            case ROUND_HALF_ODD:
                inc = (n > 5) ||
                      (n == 5 && discarded != 0) ||
                      (n == 5 && discarded == 0 && ((lsb / lsbthreshold) & 1) == 0);  // round half-odd
                break;

            case ROUND_CEIL:
                inc = (sign == 1) && (n != 0 || discarded != 0);  // round ceil
                break;

            case ROUND_FLOOR:
            default:
                inc = (sign == -1) && (n != 0 || discarded != 0);  // round floor
                break;
        }

        if (inc) {
            // increment if necessary
            int rh = lsbthreshold;
            for (int i = lsd; i < mant.length; i++) {
                final int r = mant[i] + rh;
                rh = r / RADIX;
                mant[i] = r % RADIX;
            }

            if (rh != 0) {
                shiftRight();
                mant[mant.length-1]=rh;
            }
        }

        // Check for exceptional cases and raise signals if necessary
        if (exp < MIN_EXP) {
            // Gradual Underflow
            getField().setIEEEFlagsBits(DfpField.FLAG_UNDERFLOW);
            return DfpField.FLAG_UNDERFLOW;
        }

        if (exp > MAX_EXP) {
            // Overflow
            getField().setIEEEFlagsBits(DfpField.FLAG_OVERFLOW);
            return DfpField.FLAG_OVERFLOW;
        }

        if (n != 0 || discarded != 0) {
            // Inexact
            getField().setIEEEFlagsBits(DfpField.FLAG_INEXACT);
            return DfpField.FLAG_INEXACT;
        }
        return 0;
    }

    /** {@inheritDoc} */
    @Override
    public Dfp nextAfter(Dfp x) {

        final String trapName = "nextAfter";

        // make sure we don't mix number with different precision
        if (getField().getRadixDigits() != x.getField().getRadixDigits()) {
            getField().setIEEEFlagsBits(DfpField.FLAG_INVALID);
            final Dfp result = newInstance(getZero());
            result.nans = QNAN;
            return dotrap(DfpField.FLAG_INVALID, trapName, x, result);
        }

        boolean up = false;
        Dfp result;
        Dfp inc;

        // if this is greater than x
        if (this.lessThan(x)) {
            up = true;
        }

        if (equals(x)) {
            return newInstance(x);
        }

        if (lessThan(getZero())) {
            up = !up;
        }

        if (up) {
            inc = power10(intLog10() - getDecimalDigits() + 1);
            inc = copysign(inc, this);

            if (this.equals(getZero())) {
                inc = power10K(MIN_EXP-mant.length-1);
            }

            if (inc.equals(getZero())) {
                result = copysign(newInstance(getZero()), this);
            } else {
                result = add(inc);
            }
        } else {
            inc = power10(intLog10());
            inc = copysign(inc, this);

            if (this.equals(inc)) {
                inc = inc.divide(power10(getDecimalDigits()));
            } else {
                inc = inc.divide(power10(getDecimalDigits() - 1));
            }

            if (this.equals(getZero())) {
                inc = power10K(MIN_EXP-mant.length-1);
            }

            if (inc.equals(getZero())) {
                result = copysign(newInstance(getZero()), this);
            } else {
                result = subtract(inc);
            }
        }

        if (result.classify() == INFINITE && this.classify() != INFINITE) {
            getField().setIEEEFlagsBits(DfpField.FLAG_INEXACT);
            result = dotrap(DfpField.FLAG_INEXACT, trapName, x, result);
        }

        if (result.equals(getZero()) && this.equals(getZero()) == false) {
            getField().setIEEEFlagsBits(DfpField.FLAG_INEXACT);
            result = dotrap(DfpField.FLAG_INEXACT, trapName, x, result);
        }

        return result;
    }

}
