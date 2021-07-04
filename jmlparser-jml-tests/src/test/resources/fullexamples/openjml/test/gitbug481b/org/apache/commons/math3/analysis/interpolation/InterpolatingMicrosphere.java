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

import java.util.List;
import java.util.ArrayList;
import org.apache.commons.math3.random.UnitSphereRandomVectorGenerator;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;

/**
 * Utility class for the {@link MicrosphereProjectionInterpolator} algorithm.
 *
 * @since 3.6
 */
public class InterpolatingMicrosphere {
    /** Microsphere. */
    private final List<Facet> microsphere;
    /** Microsphere data. */
    private final List<FacetData> microsphereData;
    /** Space dimension. */
    private final int dimension;
    /** Number of surface elements. */
    private final int size;
    /** Maximum fraction of the facets that can be dark. */
    private final double maxDarkFraction;
    /** Lowest non-zero illumination. */
    private final double darkThreshold;
    /** Background value. */
    private final double background;

    /**
     * Create an unitialiazed sphere.
     * Sub-classes are responsible for calling the {@code add(double[]) add}
     * method in order to initialize all the sphere's facets.
     *
     * @param dimension Dimension of the data space.
     * @param size Number of surface elements of the sphere.
     * @param maxDarkFraction Maximum fraction of the facets that can be dark.
     * If the fraction of "non-illuminated" facets is larger, no estimation
     * of the value will be performed, and the {@code background} value will
     * be returned instead.
     * @param darkThreshold Value of the illumination below which a facet is
     * considered dark.
     * @param background Value returned when the {@code maxDarkFraction}
     * threshold is exceeded.
     * @throws NotStrictlyPositiveException if {@code dimension <= 0}
     * or {@code size <= 0}.
     * @throws NotPositiveException if {@code darkThreshold < 0}.
     * @throws OutOfRangeException if {@code maxDarkFraction} does not
     * belong to the interval {@code [0, 1]}.
     */
    protected InterpolatingMicrosphere(int dimension,
                                       int size,
                                       double maxDarkFraction,
                                       double darkThreshold,
                                       double background) {
        if (dimension <= 0) {
            throw new NotStrictlyPositiveException(dimension);
        }
        if (size <= 0) {
            throw new NotStrictlyPositiveException(size);
        }
        if (maxDarkFraction < 0 ||
            maxDarkFraction > 1) {
            throw new OutOfRangeException(maxDarkFraction, 0, 1);
        }
        if (darkThreshold < 0) {
            throw new NotPositiveException(darkThreshold);
        }

        this.dimension = dimension;
        this.size = size;
        this.maxDarkFraction = maxDarkFraction;
        this.darkThreshold = darkThreshold;
        this.background = background;
        microsphere = new ArrayList<Facet>(size);
        microsphereData = new ArrayList<FacetData>(size);
    }

    /**
     * Create a sphere from randomly sampled vectors.
     *
     * @param dimension Dimension of the data space.
     * @param size Number of surface elements of the sphere.
     * @param rand Unit vector generator for creating the microsphere.
     * @param maxDarkFraction Maximum fraction of the facets that can be dark.
     * If the fraction of "non-illuminated" facets is larger, no estimation
     * of the value will be performed, and the {@code background} value will
     * be returned instead.
     * @param darkThreshold Value of the illumination below which a facet
     * is considered dark.
     * @param background Value returned when the {@code maxDarkFraction}
     * threshold is exceeded.
     * @throws DimensionMismatchException if the size of the generated
     * vectors does not match the dimension set in the constructor.
     * @throws NotStrictlyPositiveException if {@code dimension <= 0}
     * or {@code size <= 0}.
     * @throws NotPositiveException if {@code darkThreshold < 0}.
     * @throws OutOfRangeException if {@code maxDarkFraction} does not
     * belong to the interval {@code [0, 1]}.
     */
    public InterpolatingMicrosphere(int dimension,
                                    int size,
                                    double maxDarkFraction,
                                    double darkThreshold,
                                    double background,
                                    UnitSphereRandomVectorGenerator rand) {
        this(dimension, size, maxDarkFraction, darkThreshold, background);

        // Generate the microsphere normals, assuming that a number of
        // randomly generated normals will represent a sphere.
        for (int i = 0; i < size; i++) {
            add(rand.nextVector(), false);
        }
    }

    /**
     * Copy constructor.
     *
     * @param other Instance to copy.
     */
    protected InterpolatingMicrosphere(InterpolatingMicrosphere other) {
        dimension = other.dimension;
        size = other.size;
        maxDarkFraction = other.maxDarkFraction;
        darkThreshold = other.darkThreshold;
        background = other.background;

        // Field can be shared.
        microsphere = other.microsphere;

        // Field must be copied.
        microsphereData = new ArrayList<FacetData>(size);
        for (FacetData fd : other.microsphereData) {
            microsphereData.add(new FacetData(fd.illumination(), fd.sample()));
        }
    }

    /**
     * Perform a copy.
     *
     * @return a copy of this instance.
     */
    public InterpolatingMicrosphere copy() {
        return new InterpolatingMicrosphere(this);
    }

    /**
     * Get the space dimensionality.
     *
     * @return the number of space dimensions.
     */
    public int getDimension() {
        return dimension;
    }

    /**
     * Get the size of the sphere.
     *
     * @return the number of surface elements of the microspshere.
     */
    public int getSize() {
        return size;
    }

    /**
     * Estimate the value at the requested location.
     * This microsphere is placed at the given {@code point}, contribution
     * of the given {@code samplePoints} to each sphere facet is computed
     * (illumination) and the interpolation is performed (integration of
     * the illumination).
     *
     * @param point Interpolation point.
     * @param samplePoints Sampling data points.
     * @param sampleValues Sampling data values at the corresponding
     * {@code samplePoints}.
     * @param exponent Exponent used in the power law that computes
     * the weights (distance dimming factor) of the sample data.
     * @param noInterpolationTolerance When the distance between the
     * {@code point} and one of the {@code samplePoints} is less than
     * this value, no interpolation will be performed, and the value
     * of the sample will just be returned.
     * @return the estimated value at the given {@code point}.
     * @throws NotPositiveException if {@code exponent < 0}.
     */
    public double value(double[] point,
                        double[][] samplePoints,
                        double[] sampleValues,
                        double exponent,
                        double noInterpolationTolerance) {
        if (exponent < 0) {
            throw new NotPositiveException(exponent);
        }

        clear();

        // Contribution of each sample point to the illumination of the
        // microsphere's facets.
        final int numSamples = samplePoints.length;
        for (int i = 0; i < numSamples; i++) {
            // Vector between interpolation point and current sample point.
            final double[] diff = MathArrays.ebeSubtract(samplePoints[i], point);
            final double diffNorm = MathArrays.safeNorm(diff);

            if (FastMath.abs(diffNorm) < noInterpolationTolerance) {
                // No need to interpolate, as the interpolation point is
                // actually (very close to) one of the sampled points.
                return sampleValues[i];
            }

            final double weight = FastMath.pow(diffNorm, -exponent);
            illuminate(diff, sampleValues[i], weight);
        }

        return interpolate();
    }

    /**
     * Replace {@code i}-th facet of the microsphere.
     * Method for initializing the microsphere facets.
     *
     * @param normal Facet's normal vector.
     * @param copy Whether to copy the given array.
     * @throws DimensionMismatchException if the length of {@code n}
     * does not match the space dimension.
     * @throws MaxCountExceededException if the method has been called
     * more times than the size of the sphere.
     */
    protected void add(double[] normal,
                       boolean copy) {
        if (microsphere.size() >= size) {
            throw new MaxCountExceededException(size);
        }
        if (normal.length > dimension) {
            throw new DimensionMismatchException(normal.length, dimension);
        }

        microsphere.add(new Facet(copy ? normal.clone() : normal));
        microsphereData.add(new FacetData(0d, 0d));
    }

    /**
     * Interpolation.
     *
     * @return the value estimated from the current illumination of the
     * microsphere.
     */
    private double interpolate() {
        // Number of non-illuminated facets.
        int darkCount = 0;

        double value = 0;
        double totalWeight = 0;
        for (FacetData fd : microsphereData) {
            final double iV = fd.illumination();
            if (iV != 0d) {
                value += iV * fd.sample();
                totalWeight += iV;
            } else {
                ++darkCount;
            }
        }

        final double darkFraction = darkCount / (double) size;

        return darkFraction <= maxDarkFraction ?
            value / totalWeight :
            background;
    }

    /**
     * Illumination.
     *
     * @param sampleDirection Vector whose origin is at the interpolation
     * point and tail is at the sample location.
     * @param sampleValue Data value of the sample.
     * @param weight Weight.
     */
    private void illuminate(double[] sampleDirection,
                            double sampleValue,
                            double weight) {
        for (int i = 0; i < size; i++) {
            final double[] n = microsphere.get(i).getNormal();
            final double cos = MathArrays.cosAngle(n, sampleDirection);

            if (cos > 0) {
                final double illumination = cos * weight;

                if (illumination > darkThreshold &&
                    illumination > microsphereData.get(i).illumination()) {
                    microsphereData.set(i, new FacetData(illumination, sampleValue));
                }
            }
        }
    }

    /**
     * Reset the all the {@link Facet facets} data to zero.
     */
    private void clear() {
        for (int i = 0; i < size; i++) {
            microsphereData.set(i, new FacetData(0d, 0d));
        }
    }

    /**
     * Microsphere "facet" (surface element).
     */
    private static class Facet {
        /** Normal vector characterizing a surface element. */
        private final double[] normal;

        /**
         * @param n Normal vector characterizing a surface element
         * of the microsphere. No copy is made.
         */
        Facet(double[] n) {
            normal = n;
        }

        /**
         * Return a reference to the vector normal to this facet.
         *
         * @return the normal vector.
         */
        public double[] getNormal() {
            return normal;
        }
    }

    /**
     * Data associated with each {@link Facet}.
     */
    private static class FacetData {
        /** Illumination received from the sample. */
        private final double illumination;
        /** Data value of the sample. */
        private final double sample;

        /**
         * @param illumination Illumination.
         * @param sample Data value.
         */
        FacetData(double illumination, double sample) {
            this.illumination = illumination;
            this.sample = sample;
        }

        /**
         * Get the illumination.
         * @return the illumination.
         */
        public double illumination() {
            return illumination;
        }

        /**
         * Get the data value.
         * @return the data value.
         */
        public double sample() {
            return sample;
        }
    }
}
