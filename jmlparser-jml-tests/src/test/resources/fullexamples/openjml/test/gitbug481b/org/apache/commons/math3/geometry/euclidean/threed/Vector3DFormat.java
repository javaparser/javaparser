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

package org.apache.commons.math3.geometry.euclidean.threed;

import java.text.FieldPosition;
import java.text.NumberFormat;
import java.text.ParsePosition;
import java.util.Locale;

import org.apache.commons.math3.exception.MathParseException;
import org.apache.commons.math3.geometry.Vector;
import org.apache.commons.math3.geometry.VectorFormat;
import org.apache.commons.math3.util.CompositeFormat;

/**
 * Formats a 3D vector in components list format "{x; y; z}".
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
 */
public class Vector3DFormat extends VectorFormat<Euclidean3D> {

    /**
     * Create an instance with default settings.
     * <p>The instance uses the default prefix, suffix and separator:
     * "{", "}", and "; " and the default number format for components.</p>
     */
    public Vector3DFormat() {
        super(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR,
              CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with a custom number format for components.
     * @param format the custom format for components.
     */
    public Vector3DFormat(final NumberFormat format) {
        super(DEFAULT_PREFIX, DEFAULT_SUFFIX, DEFAULT_SEPARATOR, format);
    }

    /**
     * Create an instance with custom prefix, suffix and separator.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     */
    public Vector3DFormat(final String prefix, final String suffix,
                         final String separator) {
        super(prefix, suffix, separator, CompositeFormat.getDefaultNumberFormat());
    }

    /**
     * Create an instance with custom prefix, suffix, separator and format
     * for components.
     * @param prefix prefix to use instead of the default "{"
     * @param suffix suffix to use instead of the default "}"
     * @param separator separator to use instead of the default "; "
     * @param format the custom format for components.
     */
    public Vector3DFormat(final String prefix, final String suffix,
                         final String separator, final NumberFormat format) {
        super(prefix, suffix, separator, format);
    }

    /**
     * Returns the default 3D vector format for the current locale.
     * @return the default 3D vector format.
     */
    public static Vector3DFormat getInstance() {
        return getInstance(Locale.getDefault());
    }

    /**
     * Returns the default 3D vector format for the given locale.
     * @param locale the specific locale used by the format.
     * @return the 3D vector format specific to the given locale.
     */
    public static Vector3DFormat getInstance(final Locale locale) {
        return new Vector3DFormat(CompositeFormat.getDefaultNumberFormat(locale));
    }

    /**
     * Formats a {@link Vector3D} object to produce a string.
     * @param vector the object to format.
     * @param toAppendTo where the text is to be appended
     * @param pos On input: an alignment field, if desired. On output: the
     *            offsets of the alignment field
     * @return the value passed in as toAppendTo.
     */
    @Override
    public StringBuffer format(final Vector<Euclidean3D> vector, final StringBuffer toAppendTo,
                               final FieldPosition pos) {
        final Vector3D v3 = (Vector3D) vector;
        return format(toAppendTo, pos, v3.getX(), v3.getY(), v3.getZ());
    }

    /**
     * Parses a string to produce a {@link Vector3D} object.
     * @param source the string to parse
     * @return the parsed {@link Vector3D} object.
     * @throws MathParseException if the beginning of the specified string
     * cannot be parsed.
     */
    @Override
    public Vector3D parse(final String source) throws MathParseException {
        ParsePosition parsePosition = new ParsePosition(0);
        Vector3D result = parse(source, parsePosition);
        if (parsePosition.getIndex() == 0) {
            throw new MathParseException(source,
                                         parsePosition.getErrorIndex(),
                                         Vector3D.class);
        }
        return result;
    }

    /**
     * Parses a string to produce a {@link Vector3D} object.
     * @param source the string to parse
     * @param pos input/ouput parsing parameter.
     * @return the parsed {@link Vector3D} object.
     */
    @Override
    public Vector3D parse(final String source, final ParsePosition pos) {
        final double[] coordinates = parseCoordinates(3, source, pos);
        if (coordinates == null) {
            return null;
        }
        return new Vector3D(coordinates[0], coordinates[1], coordinates[2]);
    }

}
