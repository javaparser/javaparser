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

package org.apache.commons.math3.complex;

import java.text.FieldPosition;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.Locale;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathParseException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.CompositeFormat;

/**
 * Formats a Complex number in cartesian format "Re(c) + Im(c)i".  'i' can
 * be replaced with 'j' (or anything else), and the number format for both real
 * and imaginary parts can be configured.
 *
 */
public class ComplexFormat {

     /** The default imaginary character. */
    private static final String DEFAULT_IMAGINARY_CHARACTER = "i";
    /** The notation used to signify the imaginary part of the complex number. */
    private final String imaginaryCharacter;
    /** The format used for the imaginary part. */
    private final NumberFormat imaginaryFormat;
    /** The format used for the real part. */
    private final NumberFormat realFormat;

    /**
     * Create an instance with the default imaginary character, 'i', and the
     * default number format for both real and imaginary parts.
     */
    public ComplexFormat() {
        this.imaginaryCharacter = DEFAULT_IMAGINARY_CHARACTER;
        this.imaginaryFormat = CompositeFormat.getDefaultNumberFormat();
        this.realFormat = imaginaryFormat;
    }

    /**
     * Create an instance with a custom number format for both real and
     * imaginary parts.
     * @param format the custom format for both real and imaginary parts.
     * @throws NullArgumentException if {@code realFormat} is {@code null}.
     */
    public ComplexFormat(NumberFormat format) throws NullArgumentException {
        if (format == null) {
            throw new NullArgumentException(LocalizedFormats.IMAGINARY_FORMAT);
        }
        this.imaginaryCharacter = DEFAULT_IMAGINARY_CHARACTER;
        this.imaginaryFormat = format;
        this.realFormat = format;
    }

    /**
     * Create an instance with a custom number format for the real part and a
     * custom number format for the imaginary part.
     * @param realFormat the custom format for the real part.
     * @param imaginaryFormat the custom format for the imaginary part.
     * @throws NullArgumentException if {@code imaginaryFormat} is {@code null}.
     * @throws NullArgumentException if {@code realFormat} is {@code null}.
      */
    public ComplexFormat(NumberFormat realFormat, NumberFormat imaginaryFormat)
        throws NullArgumentException {
        if (imaginaryFormat == null) {
            throw new NullArgumentException(LocalizedFormats.IMAGINARY_FORMAT);
        }
        if (realFormat == null) {
            throw new NullArgumentException(LocalizedFormats.REAL_FORMAT);
        }

        this.imaginaryCharacter = DEFAULT_IMAGINARY_CHARACTER;
        this.imaginaryFormat = imaginaryFormat;
        this.realFormat = realFormat;
    }

    /**
     * Create an instance with a custom imaginary character, and the default
     * number format for both real and imaginary parts.
     * @param imaginaryCharacter The custom imaginary character.
     * @throws NullArgumentException if {@code imaginaryCharacter} is
     * {@code null}.
     * @throws NoDataException if {@code imaginaryCharacter} is an
     * empty string.
     */
    public ComplexFormat(String imaginaryCharacter)
        throws NullArgumentException, NoDataException {
        this(imaginaryCharacter, CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with a custom imaginary character, and a custom number
     * format for both real and imaginary parts.
     * @param imaginaryCharacter The custom imaginary character.
     * @param format the custom format for both real and imaginary parts.
     * @throws NullArgumentException if {@code imaginaryCharacter} is
     * {@code null}.
     * @throws NoDataException if {@code imaginaryCharacter} is an
     * empty string.
     * @throws NullArgumentException if {@code format} is {@code null}.
     */
    public ComplexFormat(String imaginaryCharacter, NumberFormat format)
        throws NullArgumentException, NoDataException {
        this(imaginaryCharacter, format, format);
    }

    /**
     * Create an instance with a custom imaginary character, a custom number
     * format for the real part, and a custom number format for the imaginary
     * part.
     *
     * @param imaginaryCharacter The custom imaginary character.
     * @param realFormat the custom format for the real part.
     * @param imaginaryFormat the custom format for the imaginary part.
     * @throws NullArgumentException if {@code imaginaryCharacter} is
     * {@code null}.
     * @throws NoDataException if {@code imaginaryCharacter} is an
     * empty string.
     * @throws NullArgumentException if {@code imaginaryFormat} is {@code null}.
     * @throws NullArgumentException if {@code realFormat} is {@code null}.
     */
    public ComplexFormat(String imaginaryCharacter,
                         NumberFormat realFormat,
                         NumberFormat imaginaryFormat)
        throws NullArgumentException, NoDataException {
        if (imaginaryCharacter == null) {
            throw new NullArgumentException();
        }
        if (imaginaryCharacter.length() == 0) {
            throw new NoDataException();
        }
        if (imaginaryFormat == null) {
            throw new NullArgumentException(LocalizedFormats.IMAGINARY_FORMAT);
        }
        if (realFormat == null) {
            throw new NullArgumentException(LocalizedFormats.REAL_FORMAT);
        }

        this.imaginaryCharacter = imaginaryCharacter;
        this.imaginaryFormat = imaginaryFormat;
        this.realFormat = realFormat;
    }

    /**
     * Get the set of locales for which complex formats are available.
     * <p>This is the same set as the {@link NumberFormat} set.</p>
     * @return available complex format locales.
     */
    public static Locale[] getAvailableLocales() {
        return NumberFormat.getAvailableLocales();
    }

    /**
     * This method calls {@link #format(Object,StringBuffer,FieldPosition)}.
     *
     * @param c Complex object to format.
     * @return A formatted number in the form "Re(c) + Im(c)i".
     */
    public String format(Complex c) {
        return format(c, new StringBuffer(), new FieldPosition(0)).toString();
    }

    /**
     * This method calls {@link #format(Object,StringBuffer,FieldPosition)}.
     *
     * @param c Double object to format.
     * @return A formatted number.
     */
    public String format(Double c) {
        return format(new Complex(c, 0), new StringBuffer(), new FieldPosition(0)).toString();
    }

    /**
     * Formats a {@link Complex} object to produce a string.
     *
     * @param complex the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     */
    public StringBuffer format(Complex complex, StringBuffer toAppendTo,
                               FieldPosition pos) {
        pos.setBeginIndex(0);
        pos.setEndIndex(0);

        // format real
        double re = complex.getReal();
        CompositeFormat.formatDouble(re, getRealFormat(), toAppendTo, pos);

        // format sign and imaginary
        double im = complex.getImaginary();
        StringBuffer imAppendTo;
        if (im < 0.0) {
            toAppendTo.append(" - ");
            imAppendTo = formatImaginary(-im, new StringBuffer(), pos);
            toAppendTo.append(imAppendTo);
            toAppendTo.append(getImaginaryCharacter());
        } else if (im > 0.0 || Double.isNaN(im)) {
            toAppendTo.append(" + ");
            imAppendTo = formatImaginary(im, new StringBuffer(), pos);
            toAppendTo.append(imAppendTo);
            toAppendTo.append(getImaginaryCharacter());
        }

        return toAppendTo;
    }

    /**
     * Format the absolute value of the imaginary part.
     *
     * @param absIm Absolute value of the imaginary part of a complex number.
     * @param toAppendTo where the text is to be appended.
     * @param pos On input: an alignment field, if desired. On output: the
     * offsets of the alignment field.
     * @return the value passed in as toAppendTo.
     */
    private StringBuffer formatImaginary(double absIm,
                                         StringBuffer toAppendTo,
                                         FieldPosition pos) {
        pos.setBeginIndex(0);
        pos.setEndIndex(0);

        CompositeFormat.formatDouble(absIm, getImaginaryFormat(), toAppendTo, pos);
        if (toAppendTo.toString().equals("1")) {
            // Remove the character "1" if it is the only one.
            toAppendTo.setLength(0);
        }

        return toAppendTo;
    }

    /**
     * Formats a object to produce a string.  {@code obj} must be either a
     * {@link Complex} object or a {@link Number} object.  Any other type of
     * object will result in an {@link IllegalArgumentException} being thrown.
     *
     * @param obj the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     * @see java.text.Format#format(java.lang.Object, java.lang.StringBuffer, java.text.FieldPosition)
     * @throws MathIllegalArgumentException is {@code obj} is not a valid type.
     */
    public StringBuffer format(Object obj, StringBuffer toAppendTo,
                               FieldPosition pos)
        throws MathIllegalArgumentException {

        StringBuffer ret = null;

        if (obj instanceof Complex) {
            ret = format( (Complex)obj, toAppendTo, pos);
        } else if (obj instanceof Number) {
            ret = format(new Complex(((Number)obj).doubleValue(), 0.0),
                         toAppendTo, pos);
        } else {
            throw new MathIllegalArgumentException(LocalizedFormats.CANNOT_FORMAT_INSTANCE_AS_COMPLEX,
                                                   obj.getClass().getName());
        }

        return ret;
    }

    /**
     * Access the imaginaryCharacter.
     * @return the imaginaryCharacter.
     */
    public String getImaginaryCharacter() {
        return imaginaryCharacter;
    }

    /**
     * Access the imaginaryFormat.
     * @return the imaginaryFormat.
     */
    public NumberFormat getImaginaryFormat() {
        return imaginaryFormat;
    }

    /**
     * Returns the default complex format for the current locale.
     * @return the default complex format.
     */
    public static ComplexFormat getInstance() {
        return getInstance(Locale.getDefault());
    }

    /**
     * Returns the default complex format for the given locale.
     * @param locale the specific locale used by the format.
     * @return the complex format specific to the given locale.
     */
    public static ComplexFormat getInstance(Locale locale) {
        NumberFormat f = CompositeFormat.getDefaultNumberFormat(locale);
        return new ComplexFormat(f);
    }

    /**
     * Returns the default complex format for the given locale.
     * @param locale the specific locale used by the format.
     * @param imaginaryCharacter Imaginary character.
     * @return the complex format specific to the given locale.
     * @throws NullArgumentException if {@code imaginaryCharacter} is
     * {@code null}.
     * @throws NoDataException if {@code imaginaryCharacter} is an
     * empty string.
     */
    public static ComplexFormat getInstance(String imaginaryCharacter, Locale locale)
        throws NullArgumentException, NoDataException {
        NumberFormat f = CompositeFormat.getDefaultNumberFormat(locale);
        return new ComplexFormat(imaginaryCharacter, f);
    }

    /**
     * Access the realFormat.
     * @return the realFormat.
     */
    public NumberFormat getRealFormat() {
        return realFormat;
    }

    /**
     * Parses a string to produce a {@link Complex} object.
     *
     * @param source the string to parse.
     * @return the parsed {@link Complex} object.
     * @throws MathParseException if the beginning of the specified string
     * cannot be parsed.
     */
    public Complex parse(String source) throws MathParseException {
        ParsePosition parsePosition = new ParsePosition(0);
        Complex result = parse(source, parsePosition);
        if (parsePosition.getIndex() == 0) {
            throw new MathParseException(source,
                                         parsePosition.getErrorIndex(),
                                         Complex.class);
        }
        return result;
    }

    /**
     * Parses a string to produce a {@link Complex} object.
     *
     * @param source the string to parse
     * @param pos input/ouput parsing parameter.
     * @return the parsed {@link Complex} object.
     */
    public Complex parse(String source, ParsePosition pos) {
        int initialIndex = pos.getIndex();

        // parse whitespace
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);

        // parse real
        Number re = CompositeFormat.parseNumber(source, getRealFormat(), pos);
        if (re == null) {
            // invalid real number
            // set index back to initial, error index should already be set
            pos.setIndex(initialIndex);
            return null;
        }

        // parse sign
        int startIndex = pos.getIndex();
        char c = CompositeFormat.parseNextCharacter(source, pos);
        int sign = 0;
        switch (c) {
        case 0 :
            // no sign
            // return real only complex number
            return new Complex(re.doubleValue(), 0.0);
        case '-' :
            sign = -1;
            break;
        case '+' :
            sign = 1;
            break;
        default :
            // invalid sign
            // set index back to initial, error index should be the last
            // character examined.
            pos.setIndex(initialIndex);
            pos.setErrorIndex(startIndex);
            return null;
        }

        // parse whitespace
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);

        // parse imaginary
        Number im = CompositeFormat.parseNumber(source, getRealFormat(), pos);
        if (im == null) {
            // invalid imaginary number
            // set index back to initial, error index should already be set
            pos.setIndex(initialIndex);
            return null;
        }

        // parse imaginary character
        if (!CompositeFormat.parseFixedstring(source, getImaginaryCharacter(), pos)) {
            return null;
        }

        return new Complex(re.doubleValue(), im.doubleValue() * sign);

    }
}
