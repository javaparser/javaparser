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
 * Generates a tricubic interpolating function.
 *
 * @since 3.4
 */
public class TricubicInterpolator
    implements TrivariateGridInterpolator {
    /**
     * {@inheritDoc}
     */
    public TricubicInterpolatingFunction interpolate(final double[] xval,
                                                     final double[] yval,
                                                     final double[] zval,
                                                     final double[][][] fval)
        throws NoDataException, NumberIsTooSmallException,
               DimensionMismatchException, NonMonotonicSequenceException {
        if (xval.length == 0 || yval.length == 0 || zval.length == 0 || fval.length == 0) {
            throw new NoDataException();
        }
        if (xval.length != fval.length) {
            throw new DimensionMismatchException(xval.length, fval.length);
        }

        MathArrays.checkOrder(xval);
        MathArrays.checkOrder(yval);
        MathArrays.checkOrder(zval);

        final int xLen = xval.length;
        final int yLen = yval.length;
        final int zLen = zval.length;

        // Approximation to the partial derivatives using finite differences.
        final double[][][] dFdX = new double[xLen][yLen][zLen];
        final double[][][] dFdY = new double[xLen][yLen][zLen];
        final double[][][] dFdZ = new double[xLen][yLen][zLen];
        final double[][][] d2FdXdY = new double[xLen][yLen][zLen];
        final double[][][] d2FdXdZ = new double[xLen][yLen][zLen];
        final double[][][] d2FdYdZ = new double[xLen][yLen][zLen];
        final double[][][] d3FdXdYdZ = new double[xLen][yLen][zLen];

        for (int i = 1; i < xLen - 1; i++) {
            if (yval.length != fval[i].length) {
                throw new DimensionMismatchException(yval.length, fval[i].length);
            }

            final int nI = i + 1;
            final int pI = i - 1;

            final double nX = xval[nI];
            final double pX = xval[pI];

            final double deltaX = nX - pX;

            for (int j = 1; j < yLen - 1; j++) {
                if (zval.length != fval[i][j].length) {
                    throw new DimensionMismatchException(zval.length, fval[i][j].length);
                }

                final int nJ = j + 1;
                final int pJ = j - 1;

                final double nY = yval[nJ];
                final double pY = yval[pJ];

                final double deltaY = nY - pY;
                final double deltaXY = deltaX * deltaY;

                for (int k = 1; k < zLen - 1; k++) {
                    final int nK = k + 1;
                    final int pK = k - 1;

                    final double nZ = zval[nK];
                    final double pZ = zval[pK];

                    final double deltaZ = nZ - pZ;

                    dFdX[i][j][k] = (fval[nI][j][k] - fval[pI][j][k]) / deltaX;
                    dFdY[i][j][k] = (fval[i][nJ][k] - fval[i][pJ][k]) / deltaY;
                    dFdZ[i][j][k] = (fval[i][j][nK] - fval[i][j][pK]) / deltaZ;

                    final double deltaXZ = deltaX * deltaZ;
                    final double deltaYZ = deltaY * deltaZ;

                    d2FdXdY[i][j][k] = (fval[nI][nJ][k] - fval[nI][pJ][k] - fval[pI][nJ][k] + fval[pI][pJ][k]) / deltaXY;
                    d2FdXdZ[i][j][k] = (fval[nI][j][nK] - fval[nI][j][pK] - fval[pI][j][nK] + fval[pI][j][pK]) / deltaXZ;
                    d2FdYdZ[i][j][k] = (fval[i][nJ][nK] - fval[i][nJ][pK] - fval[i][pJ][nK] + fval[i][pJ][pK]) / deltaYZ;

                    final double deltaXYZ = deltaXY * deltaZ;

                    d3FdXdYdZ[i][j][k] = (fval[nI][nJ][nK] - fval[nI][pJ][nK] -
                                          fval[pI][nJ][nK] + fval[pI][pJ][nK] -
                                          fval[nI][nJ][pK] + fval[nI][pJ][pK] +
                                          fval[pI][nJ][pK] - fval[pI][pJ][pK]) / deltaXYZ;
                }
            }
        }

        // Create the interpolating function.
        return new TricubicInterpolatingFunction(xval, yval, zval, fval,
                                                 dFdX, dFdY, dFdZ,
                                                 d2FdXdY, d2FdXdZ, d2FdYdZ,
                                                 d3FdXdYdZ) {
            /** {@inheritDoc} */
            @Override
            public boolean isValidPoint(double x, double y, double z) {
                if (x < xval[1] ||
                    x > xval[xval.length - 2] ||
                    y < yval[1] ||
                    y > yval[yval.length - 2] ||
                    z < zval[1] ||
                    z > zval[zval.length - 2]) {
                    return false;
                } else {
                    return true;
                }
            }
        };
    }
}
