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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.linear.ArrayRealVector;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.random.UnitSphereRandomVectorGenerator;
import org.apache.commons.math3.util.FastMath;

/**
 * Interpolating function that implements the
 * <a href="http://www.dudziak.com/microsphere.php">Microsphere Projection</a>.
 *
 * @deprecated Code will be removed in 4.0.  Use {@link InterpolatingMicrosphere}
 * and {@link MicrosphereProjectionInterpolator} instead.
 */
@Deprecated
public class MicrosphereInterpolatingFunction
    implements MultivariateFunction {
    /**
     * Space dimension.
     */
    private final int dimension;
    /**
     * Internal accounting data for the interpolation algorithm.
     * Each element of the list corresponds to one surface element of
     * the microsphere.
     */
    private final List<MicrosphereSurfaceElement> microsphere;
    /**
     * Exponent used in the power law that computes the weights of the
     * sample data.
     */
    private final double brightnessExponent;
    /**
     * Sample data.
     */
    private final Map<RealVector, Double> samples;

    /**
     * Class for storing the accounting data needed to perform the
     * microsphere projection.
     */
    private static class MicrosphereSurfaceElement {
        /** Normal vector characterizing a surface element. */
        private final RealVector normal;
        /** Illumination received from the brightest sample. */
        private double brightestIllumination;
        /** Brightest sample. */
        private Map.Entry<RealVector, Double> brightestSample;

        /**
         * @param n Normal vector characterizing a surface element
         * of the microsphere.
         */
        MicrosphereSurfaceElement(double[] n) {
            normal = new ArrayRealVector(n);
        }

        /**
         * Return the normal vector.
         * @return the normal vector
         */
        RealVector normal() {
            return normal;
        }

        /**
         * Reset "illumination" and "sampleIndex".
         */
        void reset() {
            brightestIllumination = 0;
            brightestSample = null;
        }

        /**
         * Store the illumination and index of the brightest sample.
         * @param illuminationFromSample illumination received from sample
         * @param sample current sample illuminating the element
         */
        void store(final double illuminationFromSample,
                   final Map.Entry<RealVector, Double> sample) {
            if (illuminationFromSample > this.brightestIllumination) {
                this.brightestIllumination = illuminationFromSample;
                this.brightestSample = sample;
            }
        }

        /**
         * Get the illumination of the element.
         * @return the illumination.
         */
        double illumination() {
            return brightestIllumination;
        }

        /**
         * Get the sample illuminating the element the most.
         * @return the sample.
         */
        Map.Entry<RealVector, Double> sample() {
            return brightestSample;
        }
    }

    /**
     * @param xval Arguments for the interpolation points.
     * {@code xval[i][0]} is the first component of interpolation point
     * {@code i}, {@code xval[i][1]} is the second component, and so on
     * until {@code xval[i][d-1]}, the last component of that interpolation
     * point (where {@code dimension} is thus the dimension of the sampled
     * space).
     * @param yval Values for the interpolation points.
     * @param brightnessExponent Brightness dimming factor.
     * @param microsphereElements Number of surface elements of the
     * microsphere.
     * @param rand Unit vector generator for creating the microsphere.
     * @throws DimensionMismatchException if the lengths of {@code yval} and
     * {@code xval} (equal to {@code n}, the number of interpolation points)
     * do not match, or the the arrays {@code xval[0]} ... {@code xval[n]},
     * have lengths different from {@code dimension}.
     * @throws NoDataException if there an array has zero-length.
     * @throws NullArgumentException if an argument is {@code null}.
     */
    public MicrosphereInterpolatingFunction(double[][] xval,
                                            double[] yval,
                                            int brightnessExponent,
                                            int microsphereElements,
                                            UnitSphereRandomVectorGenerator rand)
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

        dimension = xval[0].length;
        this.brightnessExponent = brightnessExponent;

        // Copy data samples.
        samples = new HashMap<RealVector, Double>(yval.length);
        for (int i = 0; i < xval.length; ++i) {
            final double[] xvalI = xval[i];
            if (xvalI == null) {
                throw new NullArgumentException();
            }
            if (xvalI.length != dimension) {
                throw new DimensionMismatchException(xvalI.length, dimension);
            }

            samples.put(new ArrayRealVector(xvalI), yval[i]);
        }

        microsphere = new ArrayList<MicrosphereSurfaceElement>(microsphereElements);
        // Generate the microsphere, assuming that a fairly large number of
        // randomly generated normals will represent a sphere.
        for (int i = 0; i < microsphereElements; i++) {
            microsphere.add(new MicrosphereSurfaceElement(rand.nextVector()));
        }
    }

    /**
     * @param point Interpolation point.
     * @return the interpolated value.
     * @throws DimensionMismatchException if point dimension does not math sample
     */
    public double value(double[] point) throws DimensionMismatchException {
        final RealVector p = new ArrayRealVector(point);

        // Reset.
        for (MicrosphereSurfaceElement md : microsphere) {
            md.reset();
        }

        // Compute contribution of each sample points to the microsphere elements illumination
        for (Map.Entry<RealVector, Double> sd : samples.entrySet()) {

            // Vector between interpolation point and current sample point.
            final RealVector diff = sd.getKey().subtract(p);
            final double diffNorm = diff.getNorm();

            if (FastMath.abs(diffNorm) < FastMath.ulp(1d)) {
                // No need to interpolate, as the interpolation point is
                // actually (very close to) one of the sampled points.
                return sd.getValue();
            }

            for (MicrosphereSurfaceElement md : microsphere) {
                final double w = FastMath.pow(diffNorm, -brightnessExponent);
                md.store(cosAngle(diff, md.normal()) * w, sd);
            }

        }

        // Interpolation calculation.
        double value = 0;
        double totalWeight = 0;
        for (MicrosphereSurfaceElement md : microsphere) {
            final double iV = md.illumination();
            final Map.Entry<RealVector, Double> sd = md.sample();
            if (sd != null) {
                value += iV * sd.getValue();
                totalWeight += iV;
            }
        }

        return value / totalWeight;
    }

    /**
     * Compute the cosine of the angle between 2 vectors.
     *
     * @param v Vector.
     * @param w Vector.
     * @return the cosine of the angle between {@code v} and {@code w}.
     */
    private double cosAngle(final RealVector v, final RealVector w) {
        return v.dotProduct(w) / (v.getNorm() * w.getNorm());
    }
}
