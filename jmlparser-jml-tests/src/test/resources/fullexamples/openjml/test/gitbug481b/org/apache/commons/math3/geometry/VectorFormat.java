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

package org.apache.commons.math3.geometry;

import java.text.FieldPosition;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.Locale;

import org.apache.commons.math3.util.CompositeFormat;
import org.apache.commons.math3.exception.MathParseException;

/**
 * Formats a vector in components list format "{x; y; ...}".
 * <p>The prefix and suffix "{" and "}" and the separator "; " can be replaced by
 * any user-defined strings. The number format for components can be configured.</p>
 * <p>White space is ignored at parse time, even if it is in the prefix, suffix
 * or separator specifications. So even if the default separator does include a space
 * character that is used at format time, both input string "{1;1;1}" and
 * " { 1 ; 1 ; 1 } " will be parsed without error and the same vector will be
 * returned. In the second case, however, the parse position after parsing will be
 * just after the closing curly brace, i.e. just before the trailing space.</p>
 * <p><b>Note:</b> using "," as a separator may interfere with the grouping separator
 * of the default {@link NumberFormat} for the current locale. Thus it is advised
 * to use a {@link NumberFormat} instance with disabled grouping in such a case.</p>
 *
 * @param <S> Type of the space.
 * @since 3.0
 */
public abstract class VectorFormat<S extends Space> {

    /** The default prefix: "{". */
    public static final String DEFAULT_PREFIX = "{";

    /** The default suffix: "}". */
    public static final String DEFAULT_SUFFIX = "}";

    /** The default separator: ", ". */
    public static final String DEFAULT_SEPARATOR = "; ";

    /** Prefix. */
    private final String prefix;

    /** Suffix. */
    private final String suffix;

    /** Separator. */
    private final String separator;

    /** Trimmed prefix. */
    private final String trimmedPrefix;

    /** Trimmed suffix. */
    private final String trimmedSuffix;

    /** Trimmed separator. */
    private final String trimmedSeparator;

    /** The format used for components. */
    private final NumberFormat format;

    /**
     * Create an instance with default settings.
     * <p>The instance uses the default prefix, suffix and separator:
     * "{", "}", and "; " and the default number format for components.</p>
     */
    protected VectorFormat() {
        this(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR,
             CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with a custom number format for components.
     * @param format the custom format for components.
     */
    protected VectorFormat(final NumberFormat format) {
        this(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR, format);
    }

    /**
     * Create an instance with custom prefix, suffix and separator.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     */
    protected VectorFormat(final String prefix, final String suffix,
                          final String separator) {
        this(prefix, suffix, separator, CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with custom prefix, suffix, separator and format
     * for components.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     * @param format the custom format for components.
     */
    protected VectorFormat(final String prefix, final String suffix,
                          final String separator, final NumberFormat format) {
        this.prefix      = prefix;
        this.suffix      = suffix;
        this.separator   = separator;
        trimmedPrefix    = prefix.trim();
        trimmedSuffix    = suffix.trim();
        trimmedSeparator = separator.trim();
        this.format      = format;
    }

    /**
     * Get the set of locales for which point/vector formats are available.
     * <p>This is the same set as the {@link NumberFormat} set.</p>
     * @return available point/vector format locales.
     */
    public static Locale[] getAvailableLocales() {
        return NumberFormat.getAvailableLocales();
    }

    /**
     * Get the format prefix.
     * @return format prefix.
     */
    public String getPrefix() {
        return prefix;
    }

    /**
     * Get the format suffix.
     * @return format suffix.
     */
    public String getSuffix() {
        return suffix;
    }

    /**
     * Get the format separator between components.
     * @return format separator.
     */
    public String getSeparator() {
        return separator;
    }

    /**
     * Get the components format.
     * @return components format.
     */
    public NumberFormat getFormat() {
        return format;
    }

    /**
     * Formats a {@link Vector} object to produce a string.
     * @param vector the object to format.
     * @return a formatted string.
     */
    public String format(Vector<S> vector) {
        return format(vector, new StringBuffer(), new FieldPosition(0)).toString();
    }

    /**
     * Formats a {@link Vector} object to produce a string.
     * @param vector the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     */
    public abstract StringBuffer format(Vector<S> vector,
                                        StringBuffer toAppendTo, FieldPosition pos);

    /**
     * Formats the coordinates of a {@link Vector} to produce a string.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @param coordinates coordinates of the object to format.
     * @return the value passed in as toAppendTo.
     */
    protected StringBuffer format(StringBuffer toAppendTo, FieldPosition pos,
                                  double ... coordinates) {

        pos.setBeginIndex(0);
        pos.setEndIndex(0);

        // format prefix
        toAppendTo.append(prefix);

        // format components
        for (int i = 0; i < coordinates.length; ++i) {
            if (i > 0) {
                toAppendTo.append(separator);
            }
            CompositeFormat.formatDouble(coordinates[i], format, toAppendTo, pos);
        }

        // format suffix
        toAppendTo.append(suffix);

        return toAppendTo;

    }

    /**
     * Parses a string to produce a {@link Vector} object.
     * @param source the string to parse
     * @return the parsed {@link Vector} object.
     * @throws MathParseException if the beginning of the specified string
     * cannot be parsed.
     */
    public abstract Vector<S> parse(String source) throws MathParseException;

    /**
     * Parses a string to produce a {@link Vector} object.
     * @param source the string to parse
     * @param pos input/output parsing parameter.
     * @return the parsed {@link Vector} object.
     */
    public abstract Vector<S> parse(String source, ParsePosition pos);

    /**
     * Parses a string to produce an array of coordinates.
     * @param dimension dimension of the space
     * @param source the string to parse
     * @param pos input/output parsing parameter.
     * @return coordinates array.
     */
    protected double[] parseCoordinates(int dimension, String source, ParsePosition pos) {

        int initialIndex = pos.getIndex();
        double[] coordinates = new double[dimension];

        // parse prefix
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);
        if (!CompositeFormat.parseFixedstring(source, trimmedPrefix, pos)) {
            return null;
        }

        for (int i = 0; i < dimension; ++i) {

            // skip whitespace
            CompositeFormat.parseAndIgnoreWhitespace(source, pos);

            // parse separator
            if (i > 0 && !CompositeFormat.parseFixedstring(source, trimmedSeparator, pos)) {
                return null;
            }

            // skip whitespace
            CompositeFormat.parseAndIgnoreWhitespace(source, pos);

            // parse coordinate
            Number c = CompositeFormat.parseNumber(source, format, pos);
            if (c == null) {
                // invalid coordinate
                // set index back to initial, error index should already be set
                pos.setIndex(initialIndex);
                return null;
            }

            // store coordinate
            coordinates[i] = c.doubleValue();

        }

        // parse suffix
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);
        if (!CompositeFormat.parseFixedstring(source, trimmedSuffix, pos)) {
            return null;
        }

        return coordinates;

    }

}
