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
package org.apache.commons.math3.geometry.euclidean.twod.hull;

import java.util.Collection;

import org.apache.commons.math3.exception.ConvergenceException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.geometry.euclidean.twod.Vector2D;
import org.apache.commons.math3.util.MathUtils;

/**
 * Abstract base class for convex hull generators in the two-dimensional euclidean space.
 *
 * @since 3.3
 */
abstract class AbstractConvexHullGenerator2D implements ConvexHullGenerator2D {

    /** Default value for tolerance. */
    private static final double DEFAULT_TOLERANCE = 1e-10;

    /** Tolerance below which points are considered identical. */
    private final double tolerance;

    /**
     * Indicates if collinear points on the hull shall be present in the output.
     * If {@code false}, only the extreme points are added to the hull.
     */
    private final boolean includeCollinearPoints;

    /**
     * Simple constructor.
     * <p>
     * The default tolerance (1e-10) will be used to determine identical points.
     *
     * @param includeCollinearPoints indicates if collinear points on the hull shall be
     * added as hull vertices
     */
    protected AbstractConvexHullGenerator2D(final boolean includeCollinearPoints) {
        this(includeCollinearPoints, DEFAULT_TOLERANCE);
    }

    /**
     * Simple constructor.
     *
     * @param includeCollinearPoints indicates if collinear points on the hull shall be
     * added as hull vertices
     * @param tolerance tolerance below which points are considered identical
     */
    protected AbstractConvexHullGenerator2D(final boolean includeCollinearPoints, final double tolerance) {
        this.includeCollinearPoints = includeCollinearPoints;
        this.tolerance = tolerance;
    }

    /**
     * Get the tolerance below which points are considered identical.
     * @return the tolerance below which points are considered identical
     */
    public double getTolerance() {
        return tolerance;
    }

    /**
     * Returns if collinear points on the hull will be added as hull vertices.
     * @return {@code true} if collinear points are added as hull vertices, or {@code false}
     * if only extreme points are present.
     */
    public boolean isIncludeCollinearPoints() {
        return includeCollinearPoints;
    }

    /** {@inheritDoc} */
    public ConvexHull2D generate(final Collection<Vector2D> points)
            throws NullArgumentException, ConvergenceException {
        // check for null points
        MathUtils.checkNotNull(points);

        Collection<Vector2D> hullVertices = null;
        if (points.size() < 2) {
            hullVertices = points;
        } else {
            hullVertices = findHullVertices(points);
        }

        try {
            return new ConvexHull2D(hullVertices.toArray(new Vector2D[hullVertices.size()]),
                                    tolerance);
        } catch (MathIllegalArgumentException e) {
            // the hull vertices may not form a convex hull if the tolerance value is to large
            throw new ConvergenceException();
        }
    }

    /**
     * Find the convex hull vertices from the set of input points.
     * @param points the set of input points
     * @return the convex hull vertices in CCW winding
     */
    protected abstract Collection<Vector2D> findHullVertices(Collection<Vector2D> points);

}
