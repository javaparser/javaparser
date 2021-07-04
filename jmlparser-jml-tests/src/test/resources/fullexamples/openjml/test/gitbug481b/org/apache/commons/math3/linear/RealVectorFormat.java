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

package org.apache.commons.math3.linear;

import java.text.FieldPosition;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import org.apache.commons.math3.exception.MathParseException;
import org.apache.commons.math3.util.CompositeFormat;

/**
 * Formats a vector in components list format "{v0; v1; ...; vk-1}".
 * <p>The prefix and suffix "{" and "}" and the separator "; " can be replaced by
 * any user-defined strings. The number format for components can be configured.</p>
 * <p>White space is ignored at parse time, even if it is in the prefix, suffix
 * or separator specifications. So even if the default separator does include a space
 * character that is used at format time, both input string "{1;1;1}" and
 * " { 1 ; 1 ; 1 } " will be parsed without error and the same vector will be
 * returned. In the second case, however, the parse position after parsing will be
 * just after the closing curly brace, i.e. just before the trailing space.</p>
 *
 * @since 2.0
 */
public class RealVectorFormat {

    /** The default prefix: "{". */
    private static final String DEFAULT_PREFIX = "{";
    /** The default suffix: "}". */
    private static final String DEFAULT_SUFFIX = "}";
    /** The default separator: ", ". */
    private static final String DEFAULT_SEPARATOR = "; ";
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
    public RealVectorFormat() {
        this(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR,
             CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with a custom number format for components.
     * @param format the custom format for components.
     */
    public RealVectorFormat(final NumberFormat format) {
        this(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR, format);
    }

    /**
     * Create an instance with custom prefix, suffix and separator.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     */
    public RealVectorFormat(final String prefix, final String suffix,
                            final String separator) {
        this(prefix, suffix, separator,
             CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with custom prefix, suffix, separator and format
     * for components.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     * @param format the custom format for components.
     */
    public RealVectorFormat(final String prefix, final String suffix,
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
     * Get the set of locales for which real vectors formats are available.
     * <p>This is the same set as the {@link NumberFormat} set.</p>
     * @return available real vector format locales.
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
     * Returns the default real vector format for the current locale.
     * @return the default real vector format.
     */
    public static RealVectorFormat getInstance() {
        return getInstance(Locale.getDefault());
    }

    /**
     * Returns the default real vector format for the given locale.
     * @param locale the specific locale used by the format.
     * @return the real vector format specific to the given locale.
     */
    public static RealVectorFormat getInstance(final Locale locale) {
        return new RealVectorFormat(CompositeFormat.getDefaultNumberFormat(locale));
    }

    /**
     * This method calls {@link #format(RealVector,StringBuffer,FieldPosition)}.
     *
     * @param v RealVector object to format.
     * @return a formatted vector.
     */
    public String format(RealVector v) {
        return format(v, new StringBuffer(), new FieldPosition(0)).toString();
    }

    /**
     * Formats a {@link RealVector} object to produce a string.
     * @param vector the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     */
    public StringBuffer format(RealVector vector, StringBuffer toAppendTo,
                               FieldPosition pos) {

        pos.setBeginIndex(0);
        pos.setEndIndex(0);

        // format prefix
        toAppendTo.append(prefix);

        // format components
        for (int i = 0; i < vector.getDimension(); ++i) {
            if (i > 0) {
                toAppendTo.append(separator);
            }
            CompositeFormat.formatDouble(vector.getEntry(i), format, toAppendTo, pos);
        }

        // format suffix
        toAppendTo.append(suffix);

        return toAppendTo;
    }

    /**
     * Parse a string to produce a {@link RealVector} object.
     *
     * @param source String to parse.
     * @return the parsed {@link RealVector} object.
     * @throws MathParseException if the beginning of the specified string
     * cannot be parsed.
     */
    public ArrayRealVector parse(String source) {
        final ParsePosition parsePosition = new ParsePosition(0);
        final ArrayRealVector result = parse(source, parsePosition);
        if (parsePosition.getIndex() == 0) {
            throw new MathParseException(source,
                                         parsePosition.getErrorIndex(),
                                         ArrayRealVector.class);
        }
        return result;
    }

    /**
     * Parse a string to produce a {@link RealVector} object.
     *
     * @param source String to parse.
     * @param pos input/ouput parsing parameter.
     * @return the parsed {@link RealVector} object.
     */
    public ArrayRealVector parse(String source, ParsePosition pos) {
        int initialIndex = pos.getIndex();

        // parse prefix
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);
        if (!CompositeFormat.parseFixedstring(source, trimmedPrefix, pos)) {
            return null;
        }

        // parse components
        List<Number> components = new ArrayList<Number>();
        for (boolean loop = true; loop;){

            if (!components.isEmpty()) {
                CompositeFormat.parseAndIgnoreWhitespace(source, pos);
                if (!CompositeFormat.parseFixedstring(source, trimmedSeparator, pos)) {
                    loop = false;
                }
            }

            if (loop) {
                CompositeFormat.parseAndIgnoreWhitespace(source, pos);
                Number component = CompositeFormat.parseNumber(source, format, pos);
                if (component != null) {
                    components.add(component);
                } else {
                    // invalid component
                    // set index back to initial, error index should already be set
                    pos.setIndex(initialIndex);
                    return null;
                }
            }

        }

        // parse suffix
        CompositeFormat.parseAndIgnoreWhitespace(source, pos);
        if (!CompositeFormat.parseFixedstring(source, trimmedSuffix, pos)) {
            return null;
        }

        // build vector
        double[] data = new double[components.size()];
        for (int i = 0; i < data.length; ++i) {
            data[i] = components.get(i).doubleValue();
        }
        return new ArrayRealVector(data, false);
    }
}
