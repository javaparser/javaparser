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
package org.apache.commons.math3.analysis.interpolation;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NonMonotonicSequenceException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.util.MathArrays;

/**
 * Generates a {@link BicubicInterpolatingFunction bicubic interpolating
 * function}.
 * <p>
 *  Caveat: Because the interpolation scheme requires that derivatives be
 *  specified at the sample points, those are approximated with finite
 *  differences (using the 2-points symmetric formulae).
 *  Since their values are undefined at the borders of the provided
 *  interpolation ranges, the interpolated values will be wrong at the
 *  edges of the patch.
 *  The {@code interpolate} method will return a function that overrides
 *  {@link BicubicInterpolatingFunction#isValidPoint(double,double)} to
 *  indicate points where the interpolation will be inaccurate.
 * </p>
 *
 * @since 3.4
 */
public class BicubicInterpolator
    implements BivariateGridInterpolator {
    /**
     * {@inheritDoc}
     */
    public BicubicInterpolatingFunction interpolate(final double[] xval,
                                                    final double[] yval,
                                                    final double[][] fval)
        throws NoDataException, DimensionMismatchException,
               NonMonotonicSequenceException, NumberIsTooSmallException {
        if (xval.length == 0 || yval.length == 0 || fval.length == 0) {
            throw new NoDataException();
        }
        if (xval.length != fval.length) {
            throw new DimensionMismatchException(xval.length, fval.length);
        }

        MathArrays.checkOrder(xval);
        MathArrays.checkOrder(yval);

        final int xLen = xval.length;
        final int yLen = yval.length;

        // Approximation to the partial derivatives using finite differences.
        final double[][] dFdX = new double[xLen][yLen];
        final double[][] dFdY = new double[xLen][yLen];
        final double[][] d2FdXdY = new double[xLen][yLen];
        for (int i = 1; i < xLen - 1; i++) {
            final int nI = i + 1;
            final int pI = i - 1;

            final double nX = xval[nI];
            final double pX = xval[pI];

            final double deltaX = nX - pX;

            for (int j = 1; j < yLen - 1; j++) {
                final int nJ = j + 1;
                final int pJ = j - 1;

                final double nY = yval[nJ];
                final double pY = yval[pJ];

                final double deltaY = nY - pY;

                dFdX[i][j] = (fval[nI][j] - fval[pI][j]) / deltaX;
                dFdY[i][j] = (fval[i][nJ] - fval[i][pJ]) / deltaY;

                final double deltaXY = deltaX * deltaY;

                d2FdXdY[i][j] = (fval[nI][nJ] - fval[nI][pJ] - fval[pI][nJ] + fval[pI][pJ]) / deltaXY;
            }
        }

        // Create the interpolating function.
        return new BicubicInterpolatingFunction(xval, yval, fval,
                                                dFdX, dFdY, d2FdXdY) {
            /** {@inheritDoc} */
            @Override
            public boolean isValidPoint(double x, double y) {
                if (x < xval[1] ||
                    x > xval[xval.length - 2] ||
                    y < yval[1] ||
                    y > yval[yval.length - 2]) {
                    return false;
                } else {
                    return true;
                }
            }
        };
    }
}
