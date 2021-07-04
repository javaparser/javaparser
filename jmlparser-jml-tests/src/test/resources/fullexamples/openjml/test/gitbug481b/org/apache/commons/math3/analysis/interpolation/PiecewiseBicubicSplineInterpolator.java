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
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.util.MathArrays;

/**
 * Generates a piecewise-bicubic interpolating function.
 *
 * @since 2.2
 */
public class PiecewiseBicubicSplineInterpolator
    implements BivariateGridInterpolator {

    /**
     * {@inheritDoc}
     */
    public PiecewiseBicubicSplineInterpolatingFunction interpolate( final double[] xval,
                                                                    final double[] yval,
                                                                    final double[][] fval)
        throws DimensionMismatchException,
               NullArgumentException,
               NoDataException,
               NonMonotonicSequenceException {
        if ( xval == null ||
             yval == null ||
             fval == null ||
             fval[0] == null ) {
            throw new NullArgumentException();
        }

        if ( xval.length == 0 ||
             yval.length == 0 ||
             fval.length == 0 ) {
            throw new NoDataException();
        }

        MathArrays.checkOrder(xval);
        MathArrays.checkOrder(yval);

        return new PiecewiseBicubicSplineInterpolatingFunction( xval, yval, fval );
    }
}
