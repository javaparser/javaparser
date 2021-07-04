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

package org.apache.commons.math3.fraction;

import java.io.Serializable;
import java.math.BigInteger;
import java.text.FieldPosition;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.Locale;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathParseException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Formats a BigFraction number in proper format or improper format.
 * <p>
 * The number format for each of the whole number, numerator and,
 * denominator can be configured.
 * </p>
 *
 * @since 2.0
 */
public class BigFractionFormat extends AbstractFormat implements Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = -2932167925527338976L;

    /**
     * Create an improper formatting instance with the default number format
     * for the numerator and denominator.
     */
    public BigFractionFormat() {
    }

    /**
     * Create an improper formatting instance with a custom number format for
     * both the numerator and denominator.
     * @param format the custom format for both the numerator and denominator.
     */
    public BigFractionFormat(final NumberFormat format) {
        super(format);
    }

    /**
     * Create an improper formatting instance with a custom number format for
     * the numerator and a custom number format for the denominator.
     * @param numeratorFormat the custom format for the numerator.
     * @param denominatorFormat the custom format for the denominator.
     */
    public BigFractionFormat(final NumberFormat numeratorFormat,
                             final NumberFormat denominatorFormat) {
        super(numeratorFormat, denominatorFormat);
    }

    /**
     * Get the set of locales for which complex formats are available.  This
     * is the same set as the {@link NumberFormat} set.
     * @return available complex format locales.
     */
    public static Locale[] getAvailableLocales() {
        return NumberFormat.getAvailableLocales();
    }

    /**
     * This static method calls formatBigFraction() on a default instance of
     * BigFractionFormat.
     *
     * @param f BigFraction object to format
     * @return A formatted BigFraction in proper form.
     */
    public static String formatBigFraction(final BigFraction f) {
        return getImproperInstance().format(f);
    }

    /**
     * Returns the default complex format for the current locale.
     * @return the default complex format.
     */
    public static BigFractionFormat getImproperInstance() {
        return getImproperInstance(Locale.getDefault());
    }

    /**
     * Returns the default complex format for the given locale.
     * @param locale the specific locale used by the format.
     * @return the complex format specific to the given locale.
     */
    public static BigFractionFormat getImproperInstance(final Locale locale) {
        return new BigFractionFormat(getDefaultNumberFormat(locale));
    }

    /**
     * Returns the default complex format for the current locale.
     * @return the default complex format.
     */
    public static BigFractionFormat getProperInstance() {
        return getProperInstance(Locale.getDefault());
    }

    /**
     * Returns the default complex format for the given locale.
     * @param locale the specific locale used by the format.
     * @return the complex format specific to the given locale.
     */
    public static BigFractionFormat getProperInstance(final Locale locale) {
        return new ProperBigFractionFormat(getDefaultNumberFormat(locale));
    }

    /**
     * Formats a {@link BigFraction} object to produce a string.  The BigFraction is
     * output in improper format.
     *
     * @param BigFraction the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     */
    public StringBuffer format(final BigFraction BigFraction,
                               final StringBuffer toAppendTo, final FieldPosition pos) {

        pos.setBeginIndex(0);
        pos.setEndIndex(0);

        getNumeratorFormat().format(BigFraction.getNumerator(), toAppendTo, pos);
        toAppendTo.append(" / ");
        getDenominatorFormat().format(BigFraction.getDenominator(), toAppendTo, pos);

        return toAppendTo;
    }

    /**
     * Formats an object and appends the result to a StringBuffer.
     * <code>obj</code> must be either a  {@link BigFraction} object or a
     * {@link BigInteger} object or a {@link Number} object. Any other type of
     * object will result in an {@link IllegalArgumentException} being thrown.
     *
     * @param obj the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     * @see java.text.Format#format(java.lang.Object, java.lang.StringBuffer, java.text.FieldPosition)
     * @throws MathIllegalArgumentException if <code>obj</code> is not a valid type.
     */
    @Override
    public StringBuffer format(final Object obj,
                               final StringBuffer toAppendTo, final FieldPosition pos) {

        final StringBuffer ret;
        if (obj instanceof BigFraction) {
            ret = format((BigFraction) obj, toAppendTo, pos);
        } else if (obj instanceof BigInteger) {
            ret = format(new BigFraction((BigInteger) obj), toAppendTo, pos);
        } else if (obj instanceof Number) {
            ret = format(new BigFraction(((Number) obj).doubleValue()),
                         toAppendTo, pos);
        } else {
            throw new MathIllegalArgumentException(LocalizedFormats.CANNOT_FORMAT_OBJECT_TO_FRACTION);
        }

        return ret;
    }

    /**
     * Parses a string to produce a {@link BigFraction} object.
     * @param source the string to parse
     * @return the parsed {@link BigFraction} object.
     * @exception MathParseException if the beginning of the specified string
     *            cannot be parsed.
     */
    @Override
    public BigFraction parse(final String source) throws MathParseException {
        final ParsePosition parsePosition = new ParsePosition(0);
        final BigFraction result = parse(source, parsePosition);
        if (parsePosition.getIndex() == 0) {
            throw new MathParseException(source, parsePosition.getErrorIndex(), BigFraction.class);
        }
        return result;
    }

    /**
     * Parses a string to produce a {@link BigFraction} object.
     * This method expects the string to be formatted as an improper BigFraction.
     * @param source the string to parse
     * @param pos input/output parsing parameter.
     * @return the parsed {@link BigFraction} object.
     */
    @Override
    public BigFraction parse(final String source, final ParsePosition pos) {
        final int initialIndex = pos.getIndex();

        // parse whitespace
        parseAndIgnoreWhitespace(source, pos);

        // parse numerator
        final BigInteger num = parseNextBigInteger(source, pos);
        if (num == null) {
            // invalid integer number
            // set index back to initial, error index should already be set
            // character examined.
            pos.setIndex(initialIndex);
            return null;
        }

        // parse '/'
        final int startIndex = pos.getIndex();
        final char c = parseNextCharacter(source, pos);
        switch (c) {
        case 0 :
            // no '/'
            // return num as a BigFraction
            return new BigFraction(num);
        case '/' :
            // found '/', continue parsing denominator
            break;
        default :
            // invalid '/'
            // set index back to initial, error index should be the last
            // character examined.
            pos.setIndex(initialIndex);
            pos.setErrorIndex(startIndex);
            return null;
        }

        // parse whitespace
        parseAndIgnoreWhitespace(source, pos);

        // parse denominator
        final BigInteger den = parseNextBigInteger(source, pos);
        if (den == null) {
            // invalid integer number
            // set index back to initial, error index should already be set
            // character examined.
            pos.setIndex(initialIndex);
            return null;
        }

        return new BigFraction(num, den);
    }

    /**
     * Parses a string to produce a <code>BigInteger</code>.
     * @param source the string to parse
     * @param pos input/output parsing parameter.
     * @return a parsed <code>BigInteger</code> or null if string does not
     * contain a BigInteger at the specified position
     */
    protected BigInteger parseNextBigInteger(final String source,
                                             final ParsePosition pos) {

        final int start = pos.getIndex();
         int end = (source.charAt(start) == '-') ? (start + 1) : start;
         while((end < source.length()) &&
               Character.isDigit(source.charAt(end))) {
             ++end;
         }

         try {
             BigInteger n = new BigInteger(source.substring(start, end));
             pos.setIndex(end);
             return n;
         } catch (NumberFormatException nfe) {
             pos.setErrorIndex(start);
             return null;
         }

    }

}
