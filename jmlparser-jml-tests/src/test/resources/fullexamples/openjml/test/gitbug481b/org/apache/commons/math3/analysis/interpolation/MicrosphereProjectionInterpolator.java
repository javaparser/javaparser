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

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.random.UnitSphereRandomVectorGenerator;

/**
 * Interpolator that implements the algorithm described in
 * <em>William Dudziak</em>'s
 * <a href="http://www.dudziak.com/microsphere.pdf">MS thesis</a>.
 *
 * @since 3.6
 */
public class MicrosphereProjectionInterpolator
    implements MultivariateInterpolator {
    /** Brightness exponent. */
    private final double exponent;
    /** Microsphere. */
    private final InterpolatingMicrosphere microsphere;
    /** Whether to share the sphere. */
    private final boolean sharedSphere;
    /** Tolerance value below which no interpolation is necessary. */
    private final double noInterpolationTolerance;

    /**
     * Create a microsphere interpolator.
     *
     * @param dimension Space dimension.
     * @param elements Number of surface elements of the microsphere.
     * @param exponent Exponent used in the power law that computes the
     * @param maxDarkFraction Maximum fraction of the facets that can be dark.
     * If the fraction of "non-illuminated" facets is larger, no estimation
     * of the value will be performed, and the {@code background} value will
     * be returned instead.
     * @param darkThreshold Value of the illumination below which a facet is
     * considered dark.
     * @param background Value returned when the {@code maxDarkFraction}
     * threshold is exceeded.
     * @param sharedSphere Whether the sphere can be shared among the
     * interpolating function instances.  If {@code true}, the instances
     * will share the same data, and thus will <em>not</em> be thread-safe.
     * @param noInterpolationTolerance When the distance between an
     * interpolated point and one of the sample points is less than this
     * value, no interpolation will be performed (the value of the sample
     * will be returned).
     * @throws org.apache.commons.math3.exception.NotStrictlyPositiveException
     * if {@code dimension <= 0} or {@code elements <= 0}.
     * @throws NotPositiveException if {@code exponent < 0}.
     * @throws NotPositiveException if {@code darkThreshold < 0}.
     * @throws org.apache.commons.math3.exception.OutOfRangeException if
     * {@code maxDarkFraction} does not belong to the interval {@code [0, 1]}.
     */
    public MicrosphereProjectionInterpolator(int dimension,
                                             int elements,
                                             double maxDarkFraction,
                                             double darkThreshold,
                                             double background,
                                             double exponent,
                                             boolean sharedSphere,
                                             double noInterpolationTolerance) {
        this(new InterpolatingMicrosphere(dimension,
                                          elements,
                                          maxDarkFraction,
                                          darkThreshold,
                                          background,
                                          new UnitSphereRandomVectorGenerator(dimension)),
             exponent,
             sharedSphere,
             noInterpolationTolerance);
    }

    /**
     * Create a microsphere interpolator.
     *
     * @param microsphere Microsphere.
     * @param exponent Exponent used in the power law that computes the
     * weights (distance dimming factor) of the sample data.
     * @param sharedSphere Whether the sphere can be shared among the
     * interpolating function instances.  If {@code true}, the instances
     * will share the same data, and thus will <em>not</em> be thread-safe.
     * @param noInterpolationTolerance When the distance between an
     * interpolated point and one of the sample points is less than this
     * value, no interpolation will be performed (the value of the sample
     * will be returned).
     * @throws NotPositiveException if {@code exponent < 0}.
     */
    public MicrosphereProjectionInterpolator(InterpolatingMicrosphere microsphere,
                                             double exponent,
                                             boolean sharedSphere,
                                             double noInterpolationTolerance)
        throws NotPositiveException {
        if (exponent < 0) {
            throw new NotPositiveException(exponent);
        }

        this.microsphere = microsphere;
        this.exponent = exponent;
        this.sharedSphere = sharedSphere;
        this.noInterpolationTolerance = noInterpolationTolerance;
    }

    /**
     * {@inheritDoc}
     *
     * @throws DimensionMismatchException if the space dimension of the
     * given samples does not match the space dimension of the microsphere.
     */
    public MultivariateFunction interpolate(final double[][] xval,
                                            final double[] yval)
        throws DimensionMismatchException,
               NoDataException,
               NullArgumentException {
        if (xval == null ||
            yval == null) {
            throw new NullArgumentException();
        }
        if (xval.length == 0) {
            throw new NoDataException();
        }
        if (xval.length != yval.length) {
            throw new DimensionMismatchException(xval.length, yval.length);
        }
        if (xval[0] == null) {
            throw new NullArgumentException();
        }
        final int dimension = microsphere.getDimension();
        if (dimension != xval[0].length) {
            throw new DimensionMismatchException(xval[0].length, dimension);
        }

        // Microsphere copy.
        final InterpolatingMicrosphere m = sharedSphere ? microsphere : microsphere.copy();

        return new MultivariateFunction() {
            /** {inheritDoc} */
            public double value(double[] point) {
                return m.value(point,
                               xval,
                               yval,
                               exponent,
                               noInterpolationTolerance);
            }
        };
    }
}
