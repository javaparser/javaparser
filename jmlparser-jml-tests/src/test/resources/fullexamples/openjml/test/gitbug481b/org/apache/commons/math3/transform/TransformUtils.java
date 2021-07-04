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
package org.apache.commons.math3.transform;

import java.util.Arrays;

import org.apache.commons.math3.complex.Complex;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Useful functions for the implementation of various transforms.
 *
 * @since 3.0
 */
public class TransformUtils {
    /**
     * Table of the powers of 2 to facilitate binary search lookup.
     *
     * @see #exactLog2(int)
     */
    private static final int[] POWERS_OF_TWO = {
        0x00000001, 0x00000002, 0x00000004, 0x00000008, 0x00000010, 0x00000020,
        0x00000040, 0x00000080, 0x00000100, 0x00000200, 0x00000400, 0x00000800,
        0x00001000, 0x00002000, 0x00004000, 0x00008000, 0x00010000, 0x00020000,
        0x00040000, 0x00080000, 0x00100000, 0x00200000, 0x00400000, 0x00800000,
        0x01000000, 0x02000000, 0x04000000, 0x08000000, 0x10000000, 0x20000000,
        0x40000000
    };

    /** Private constructor. */
    private TransformUtils() {
        super();
    }

    /**
     * Multiply every component in the given real array by the
     * given real number. The change is made in place.
     *
     * @param f the real array to be scaled
     * @param d the real scaling coefficient
     * @return a reference to the scaled array
     */
    public static double[] scaleArray(double[] f, double d) {

        for (int i = 0; i < f.length; i++) {
            f[i] *= d;
        }
        return f;
    }

    /**
     * Multiply every component in the given complex array by the
     * given real number. The change is made in place.
     *
     * @param f the complex array to be scaled
     * @param d the real scaling coefficient
     * @return a reference to the scaled array
     */
    public static Complex[] scaleArray(Complex[] f, double d) {

        for (int i = 0; i < f.length; i++) {
            f[i] = new Complex(d * f[i].getReal(), d * f[i].getImaginary());
        }
        return f;
    }


    /**
     * Builds a new two dimensional array of {@code double} filled with the real
     * and imaginary parts of the specified {@link Complex} numbers. In the
     * returned array {@code dataRI}, the data is laid out as follows
     * <ul>
     * <li>{@code dataRI[0][i] = dataC[i].getReal()},</li>
     * <li>{@code dataRI[1][i] = dataC[i].getImaginary()}.</li>
     * </ul>
     *
     * @param dataC the array of {@link Complex} data to be transformed
     * @return a two dimensional array filled with the real and imaginary parts
     *   of the specified complex input
     */
    public static double[][] createRealImaginaryArray(final Complex[] dataC) {
        final double[][] dataRI = new double[2][dataC.length];
        final double[] dataR = dataRI[0];
        final double[] dataI = dataRI[1];
        for (int i = 0; i < dataC.length; i++) {
            final Complex c = dataC[i];
            dataR[i] = c.getReal();
            dataI[i] = c.getImaginary();
        }
        return dataRI;
    }

    /**
     * Builds a new array of {@link Complex} from the specified two dimensional
     * array of real and imaginary parts. In the returned array {@code dataC},
     * the data is laid out as follows
     * <ul>
     * <li>{@code dataC[i].getReal() = dataRI[0][i]},</li>
     * <li>{@code dataC[i].getImaginary() = dataRI[1][i]}.</li>
     * </ul>
     *
     * @param dataRI the array of real and imaginary parts to be transformed
     * @return an array of {@link Complex} with specified real and imaginary parts.
     * @throws DimensionMismatchException if the number of rows of the specified
     *   array is not two, or the array is not rectangular
     */
    public static Complex[] createComplexArray(final double[][] dataRI)
        throws DimensionMismatchException{

        if (dataRI.length != 2) {
            throw new DimensionMismatchException(dataRI.length, 2);
        }
        final double[] dataR = dataRI[0];
        final double[] dataI = dataRI[1];
        if (dataR.length != dataI.length) {
            throw new DimensionMismatchException(dataI.length, dataR.length);
        }

        final int n = dataR.length;
        final Complex[] c = new Complex[n];
        for (int i = 0; i < n; i++) {
            c[i] = new Complex(dataR[i], dataI[i]);
        }
        return c;
    }


    /**
     * Returns the base-2 logarithm of the specified {@code int}. Throws an
     * exception if {@code n} is not a power of two.
     *
     * @param n the {@code int} whose base-2 logarithm is to be evaluated
     * @return the base-2 logarithm of {@code n}
     * @throws MathIllegalArgumentException if {@code n} is not a power of two
     */
    public static int exactLog2(final int n)
        throws MathIllegalArgumentException {

        int index = Arrays.binarySearch(TransformUtils.POWERS_OF_TWO, n);
        if (index < 0) {
            throw new MathIllegalArgumentException(
                    LocalizedFormats.NOT_POWER_OF_TWO_CONSIDER_PADDING,
                    Integer.valueOf(n));
        }
        return index;
    }
}
