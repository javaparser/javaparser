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
package org.apache.commons.math3.geometry.partitioning.utilities;

import java.util.Arrays;

import org.apache.commons.math3.util.FastMath;

/** This class implements an ordering operation for T-uples.
 *
 * <p>Ordering is done by encoding all components of the T-uple into a
 * single scalar value and using this value as the sorting
 * key. Encoding is performed using the method invented by Georg
 * Cantor in 1877 when he proved it was possible to establish a
 * bijection between a line and a plane. The binary representations of
 * the components of the T-uple are mixed together to form a single
 * scalar. This means that the 2<sup>k</sup> bit of component 0 is
 * followed by the 2<sup>k</sup> bit of component 1, then by the
 * 2<sup>k</sup> bit of component 2 up to the 2<sup>k</sup> bit of
 * component {@code t}, which is followed by the 2<sup>k-1</sup>
 * bit of component 0, followed by the 2<sup>k-1</sup> bit of
 * component 1 ... The binary representations are extended as needed
 * to handle numbers with different scales and a suitable
 * 2<sup>p</sup> offset is added to the components in order to avoid
 * negative numbers (this offset is adjusted as needed during the
 * comparison operations).</p>
 *
 * <p>The more interesting property of the encoding method for our
 * purpose is that it allows to select all the points that are in a
 * given range. This is depicted in dimension 2 by the following
 * picture:</p>
 *
 * <img src="doc-files/OrderedTuple.png" />
 *
 * <p>This picture shows a set of 100000 random 2-D pairs having their
 * first component between -50 and +150 and their second component
 * between -350 and +50. We wanted to extract all pairs having their
 * first component between +30 and +70 and their second component
 * between -120 and -30. We built the lower left point at coordinates
 * (30, -120) and the upper right point at coordinates (70, -30). All
 * points smaller than the lower left point are drawn in red and all
 * points larger than the upper right point are drawn in blue. The
 * green points are between the two limits. This picture shows that
 * all the desired points are selected, along with spurious points. In
 * this case, we get 15790 points, 4420 of which really belonging to
 * the desired rectangle. It is possible to extract very small
 * subsets. As an example extracting from the same 100000 points set
 * the points having their first component between +30 and +31 and
 * their second component between -91 and -90, we get a subset of 11
 * points, 2 of which really belonging to the desired rectangle.</p>
 *
 * <p>the previous selection technique can be applied in all
 * dimensions, still using two points to define the interval. The
 * first point will have all its components set to their lower bounds
 * while the second point will have all its components set to their
 * upper bounds.</p>
 *
 * <p>T-uples with negative infinite or positive infinite components
 * are sorted logically.</p>
 *
 * <p>Since the specification of the {@code Comparator} interface
 * allows only {@code ClassCastException} errors, some arbitrary
 * choices have been made to handle specific cases. The rationale for
 * these choices is to keep <em>regular</em> and consistent T-uples
 * together.</p>
 * <ul>
 * <li>instances with different dimensions are sorted according to
 * their dimension regardless of their components values</li>
 * <li>instances with {@code Double.NaN} components are sorted
 * after all other ones (even after instances with positive infinite
 * components</li>
 * <li>instances with both positive and negative infinite components
 * are considered as if they had {@code Double.NaN}
 * components</li>
 * </ul>
 *
 * @since 3.0
 * @deprecated as of 3.4, this class is not used anymore and considered
 * to be out of scope of Apache Commons Math
 */
@Deprecated
public class OrderedTuple implements Comparable<OrderedTuple> {

    /** Sign bit mask. */
    private static final long SIGN_MASK     = 0x8000000000000000L;

    /** Exponent bits mask. */
    private static final long EXPONENT_MASK = 0x7ff0000000000000L;

    /** Mantissa bits mask. */
    private static final long MANTISSA_MASK = 0x000fffffffffffffL;

    /** Implicit MSB for normalized numbers. */
    private static final long IMPLICIT_ONE  = 0x0010000000000000L;

    /** Double components of the T-uple. */
    private double[] components;

    /** Offset scale. */
    private int offset;

    /** Least Significant Bit scale. */
    private int lsb;

    /** Ordering encoding of the double components. */
    private long[] encoding;

    /** Positive infinity marker. */
    private boolean posInf;

    /** Negative infinity marker. */
    private boolean negInf;

    /** Not A Number marker. */
    private boolean nan;

    /** Build an ordered T-uple from its components.
     * @param components double components of the T-uple
     */
    public OrderedTuple(final double ... components) {
        this.components = components.clone();
        int msb = Integer.MIN_VALUE;
        lsb     = Integer.MAX_VALUE;
        posInf  = false;
        negInf  = false;
        nan     = false;
        for (int i = 0; i < components.length; ++i) {
            if (Double.isInfinite(components[i])) {
                if (components[i] < 0) {
                    negInf = true;
                } else {
                    posInf = true;
                }
            } else if (Double.isNaN(components[i])) {
                nan = true;
            } else {
                final long b = Double.doubleToLongBits(components[i]);
                final long m = mantissa(b);
                if (m != 0) {
                    final int e = exponent(b);
                    msb = FastMath.max(msb, e + computeMSB(m));
                    lsb = FastMath.min(lsb, e + computeLSB(m));
                }
            }
        }

        if (posInf && negInf) {
            // instance cannot be sorted logically
            posInf = false;
            negInf = false;
            nan    = true;
        }

        if (lsb <= msb) {
            // encode the T-upple with the specified offset
            encode(msb + 16);
        } else {
            encoding = new long[] {
                0x0L
            };
        }

    }

    /** Encode the T-uple with a given offset.
     * @param minOffset minimal scale of the offset to add to all
     * components (must be greater than the MSBs of all components)
     */
    private void encode(final int minOffset) {

        // choose an offset with some margins
        offset  = minOffset + 31;
        offset -= offset % 32;

        if ((encoding != null) && (encoding.length == 1) && (encoding[0] == 0x0L)) {
            // the components are all zeroes
            return;
        }

        // allocate an integer array to encode the components (we use only
        // 63 bits per element because there is no unsigned long in Java)
        final int neededBits  = offset + 1 - lsb;
        final int neededLongs = (neededBits + 62) / 63;
        encoding = new long[components.length * neededLongs];

        // mix the bits from all components
        int  eIndex = 0;
        int  shift  = 62;
        long word   = 0x0L;
        for (int k = offset; eIndex < encoding.length; --k) {
            for (int vIndex = 0; vIndex < components.length; ++vIndex) {
                if (getBit(vIndex, k) != 0) {
                    word |= 0x1L << shift;
                }
                if (shift-- == 0) {
                    encoding[eIndex++] = word;
                    word  = 0x0L;
                    shift = 62;
                }
            }
        }

    }

    /** Compares this ordered T-uple with the specified object.

     * <p>The ordering method is detailed in the general description of
     * the class. Its main property is to be consistent with distance:
     * geometrically close T-uples stay close to each other when stored
     * in a sorted collection using this comparison method.</p>

     * <p>T-uples with negative infinite, positive infinite are sorted
     * logically.</p>

     * <p>Some arbitrary choices have been made to handle specific
     * cases. The rationale for these choices is to keep
     * <em>normal</em> and consistent T-uples together.</p>
     * <ul>
     * <li>instances with different dimensions are sorted according to
     * their dimension regardless of their components values</li>
     * <li>instances with {@code Double.NaN} components are sorted
     * after all other ones (evan after instances with positive infinite
     * components</li>
     * <li>instances with both positive and negative infinite components
     * are considered as if they had {@code Double.NaN}
     * components</li>
     * </ul>

     * @param ot T-uple to compare instance with
     * @return a negative integer if the instance is less than the
     * object, zero if they are equal, or a positive integer if the
     * instance is greater than the object

     */
    public int compareTo(final OrderedTuple ot) {
        if (components.length == ot.components.length) {
            if (nan) {
                return +1;
            } else if (ot.nan) {
                return -1;
            } else if (negInf || ot.posInf) {
                return -1;
            } else if (posInf || ot.negInf) {
                return +1;
            } else {

                if (offset < ot.offset) {
                    encode(ot.offset);
                } else if (offset > ot.offset) {
                    ot.encode(offset);
                }

                final int limit = FastMath.min(encoding.length, ot.encoding.length);
                for (int i = 0; i < limit; ++i) {
                    if (encoding[i] < ot.encoding[i]) {
                        return -1;
                    } else if (encoding[i] > ot.encoding[i]) {
                        return +1;
                    }
                }

                if (encoding.length < ot.encoding.length) {
                    return -1;
                } else if (encoding.length > ot.encoding.length) {
                    return +1;
                } else {
                    return 0;
                }

            }
        }

        return components.length - ot.components.length;

    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        } else if (other instanceof OrderedTuple) {
            return compareTo((OrderedTuple) other) == 0;
        } else {
            return false;
        }
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        // the following constants are arbitrary small primes
        final int multiplier = 37;
        final int trueHash   = 97;
        final int falseHash  = 71;

        // hash fields and combine them
        // (we rely on the multiplier to have different combined weights
        //  for all int fields and all boolean fields)
        int hash = Arrays.hashCode(components);
        hash = hash * multiplier + offset;
        hash = hash * multiplier + lsb;
        hash = hash * multiplier + (posInf ? trueHash : falseHash);
        hash = hash * multiplier + (negInf ? trueHash : falseHash);
        hash = hash * multiplier + (nan    ? trueHash : falseHash);

        return hash;

    }

    /** Get the components array.
     * @return array containing the T-uple components
     */
    public double[] getComponents() {
        return components.clone();
    }

    /** Extract the sign from the bits of a double.
     * @param bits binary representation of the double
     * @return sign bit (zero if positive, non zero if negative)
     */
    private static long sign(final long bits) {
        return bits & SIGN_MASK;
    }

    /** Extract the exponent from the bits of a double.
     * @param bits binary representation of the double
     * @return exponent
     */
    private static int exponent(final long bits) {
        return ((int) ((bits & EXPONENT_MASK) >> 52)) - 1075;
    }

    /** Extract the mantissa from the bits of a double.
     * @param bits binary representation of the double
     * @return mantissa
     */
    private static long mantissa(final long bits) {
        return ((bits & EXPONENT_MASK) == 0) ?
               ((bits & MANTISSA_MASK) << 1) :          // subnormal number
               (IMPLICIT_ONE | (bits & MANTISSA_MASK)); // normal number
    }

    /** Compute the most significant bit of a long.
     * @param l long from which the most significant bit is requested
     * @return scale of the most significant bit of {@code l},
     * or 0 if {@code l} is zero
     * @see #computeLSB
     */
    private static int computeMSB(final long l) {

        long ll = l;
        long mask  = 0xffffffffL;
        int  scale = 32;
        int  msb   = 0;

        while (scale != 0) {
            if ((ll & mask) != ll) {
                msb |= scale;
                ll >>= scale;
            }
            scale >>= 1;
            mask >>= scale;
        }

        return msb;

    }

    /** Compute the least significant bit of a long.
     * @param l long from which the least significant bit is requested
     * @return scale of the least significant bit of {@code l},
     * or 63 if {@code l} is zero
     * @see #computeMSB
     */
    private static int computeLSB(final long l) {

        long ll = l;
        long mask  = 0xffffffff00000000L;
        int  scale = 32;
        int  lsb   = 0;

        while (scale != 0) {
            if ((ll & mask) == ll) {
                lsb |= scale;
                ll >>= scale;
            }
            scale >>= 1;
            mask >>= scale;
        }

        return lsb;

    }

    /** Get a bit from the mantissa of a double.
     * @param i index of the component
     * @param k scale of the requested bit
     * @return the specified bit (either 0 or 1), after the offset has
     * been added to the double
     */
    private int getBit(final int i, final int k) {
        final long bits = Double.doubleToLongBits(components[i]);
        final int e = exponent(bits);
        if ((k < e) || (k > offset)) {
            return 0;
        } else if (k == offset) {
            return (sign(bits) == 0L) ? 1 : 0;
        } else if (k > (e + 52)) {
            return (sign(bits) == 0L) ? 0 : 1;
        } else {
            final long m = (sign(bits) == 0L) ? mantissa(bits) : -mantissa(bits);
            return (int) ((m >> (k - e)) & 0x1L);
        }
    }

}
