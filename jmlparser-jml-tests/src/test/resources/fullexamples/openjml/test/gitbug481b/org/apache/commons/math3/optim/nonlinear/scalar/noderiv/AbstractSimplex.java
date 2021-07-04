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

package org.apache.commons.math3.optim.nonlinear.scalar.noderiv;

import java.util.Arrays;
import java.util.Comparator;

import org.apache.commons.math3.analysis.MultivariateFunction;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.optim.PointValuePair;
import org.apache.commons.math3.optim.OptimizationData;

/**
 * This class implements the simplex concept.
 * It is intended to be used in conjunction with {@link SimplexOptimizer}.
 * <br/>
 * The initial configuration of the simplex is set by the constructors
 * {@link #AbstractSimplex(double[])} or {@link #AbstractSimplex(double[][])}.
 * The other {@link #AbstractSimplex(int) constructor} will set all steps
 * to 1, thus building a default configuration from a unit hypercube.
 * <br/>
 * Users <em>must</em> call the {@link #build(double[]) build} method in order
 * to create the data structure that will be acted on by the other methods of
 * this class.
 *
 * @see SimplexOptimizer
 * @since 3.0
 */
public abstract class AbstractSimplex implements OptimizationData {
    /** Simplex. */
    private PointValuePair[] simplex;
    /** Start simplex configuration. */
    private double[][] startConfiguration;
    /** Simplex dimension (must be equal to {@code simplex.length - 1}). */
    private final int dimension;

    /**
     * Build a unit hypercube simplex.
     *
     * @param n Dimension of the simplex.
     */
    protected AbstractSimplex(int n) {
        this(n, 1d);
    }

    /**
     * Build a hypercube simplex with the given side length.
     *
     * @param n Dimension of the simplex.
     * @param sideLength Length of the sides of the hypercube.
     */
    protected AbstractSimplex(int n,
                              double sideLength) {
        this(createHypercubeSteps(n, sideLength));
    }

    /**
     * The start configuration for simplex is built from a box parallel to
     * the canonical axes of the space. The simplex is the subset of vertices
     * of a box parallel to the canonical axes. It is built as the path followed
     * while traveling from one vertex of the box to the diagonally opposite
     * vertex moving only along the box edges. The first vertex of the box will
     * be located at the start point of the optimization.
     * As an example, in dimension 3 a simplex has 4 vertices. Setting the
     * steps to (1, 10, 2) and the start point to (1, 1, 1) would imply the
     * start simplex would be: { (1, 1, 1), (2, 1, 1), (2, 11, 1), (2, 11, 3) }.
     * The first vertex would be set to the start point at (1, 1, 1) and the
     * last vertex would be set to the diagonally opposite vertex at (2, 11, 3).
     *
     * @param steps Steps along the canonical axes representing box edges. They
     * may be negative but not zero.
     * @throws NullArgumentException if {@code steps} is {@code null}.
     * @throws ZeroException if one of the steps is zero.
     */
    protected AbstractSimplex(final double[] steps) {
        if (steps == null) {
            throw new NullArgumentException();
        }
        if (steps.length == 0) {
            throw new ZeroException();
        }
        dimension = steps.length;

        // Only the relative position of the n final vertices with respect
        // to the first one are stored.
        startConfiguration = new double[dimension][dimension];
        for (int i = 0; i < dimension; i++) {
            final double[] vertexI = startConfiguration[i];
            for (int j = 0; j < i + 1; j++) {
                if (steps[j] == 0) {
                    throw new ZeroException(LocalizedFormats.EQUAL_VERTICES_IN_SIMPLEX);
                }
                System.arraycopy(steps, 0, vertexI, 0, j + 1);
            }
        }
    }

    /**
     * The real initial simplex will be set up by moving the reference
     * simplex such that its first point is located at the start point of the
     * optimization.
     *
     * @param referenceSimplex Reference simplex.
     * @throws NotStrictlyPositiveException if the reference simplex does not
     * contain at least one point.
     * @throws DimensionMismatchException if there is a dimension mismatch
     * in the reference simplex.
     * @throws IllegalArgumentException if one of its vertices is duplicated.
     */
    protected AbstractSimplex(final double[][] referenceSimplex) {
        if (referenceSimplex.length <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.SIMPLEX_NEED_ONE_POINT,
                                                   referenceSimplex.length);
        }
        dimension = referenceSimplex.length - 1;

        // Only the relative position of the n final vertices with respect
        // to the first one are stored.
        startConfiguration = new double[dimension][dimension];
        final double[] ref0 = referenceSimplex[0];

        // Loop over vertices.
        for (int i = 0; i < referenceSimplex.length; i++) {
            final double[] refI = referenceSimplex[i];

            // Safety checks.
            if (refI.length != dimension) {
                throw new DimensionMismatchException(refI.length, dimension);
            }
            for (int j = 0; j < i; j++) {
                final double[] refJ = referenceSimplex[j];
                boolean allEquals = true;
                for (int k = 0; k < dimension; k++) {
                    if (refI[k] != refJ[k]) {
                        allEquals = false;
                        break;
                    }
                }
                if (allEquals) {
                    throw new MathIllegalArgumentException(LocalizedFormats.EQUAL_VERTICES_IN_SIMPLEX,
                                                           i, j);
                }
            }

            // Store vertex i position relative to vertex 0 position.
            if (i > 0) {
                final double[] confI = startConfiguration[i - 1];
                for (int k = 0; k < dimension; k++) {
                    confI[k] = refI[k] - ref0[k];
                }
            }
        }
    }

    /**
     * Get simplex dimension.
     *
     * @return the dimension of the simplex.
     */
    public int getDimension() {
        return dimension;
    }

    /**
     * Get simplex size.
     * After calling the {@link #build(double[]) build} method, this method will
     * will be equivalent to {@code getDimension() + 1}.
     *
     * @return the size of the simplex.
     */
    public int getSize() {
        return simplex.length;
    }

    /**
     * Compute the next simplex of the algorithm.
     *
     * @param evaluationFunction Evaluation function.
     * @param comparator Comparator to use to sort simplex vertices from best
     * to worst.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the algorithm fails to converge.
     */
    public abstract void iterate(final MultivariateFunction evaluationFunction,
                                 final Comparator<PointValuePair> comparator);

    /**
     * Build an initial simplex.
     *
     * @param startPoint First point of the simplex.
     * @throws DimensionMismatchException if the start point does not match
     * simplex dimension.
     */
    public void build(final double[] startPoint) {
        if (dimension != startPoint.length) {
            throw new DimensionMismatchException(dimension, startPoint.length);
        }

        // Set first vertex.
        simplex = new PointValuePair[dimension + 1];
        simplex[0] = new PointValuePair(startPoint, Double.NaN);

        // Set remaining vertices.
        for (int i = 0; i < dimension; i++) {
            final double[] confI = startConfiguration[i];
            final double[] vertexI = new double[dimension];
            for (int k = 0; k < dimension; k++) {
                vertexI[k] = startPoint[k] + confI[k];
            }
            simplex[i + 1] = new PointValuePair(vertexI, Double.NaN);
        }
    }

    /**
     * Evaluate all the non-evaluated points of the simplex.
     *
     * @param evaluationFunction Evaluation function.
     * @param comparator Comparator to use to sort simplex vertices from best to worst.
     * @throws org.apache.commons.math3.exception.TooManyEvaluationsException
     * if the maximal number of evaluations is exceeded.
     */
    public void evaluate(final MultivariateFunction evaluationFunction,
                         final Comparator<PointValuePair> comparator) {
        // Evaluate the objective function at all non-evaluated simplex points.
        for (int i = 0; i < simplex.length; i++) {
            final PointValuePair vertex = simplex[i];
            final double[] point = vertex.getPointRef();
            if (Double.isNaN(vertex.getValue())) {
                simplex[i] = new PointValuePair(point, evaluationFunction.value(point), false);
            }
        }

        // Sort the simplex from best to worst.
        Arrays.sort(simplex, comparator);
    }

    /**
     * Replace the worst point of the simplex by a new point.
     *
     * @param pointValuePair Point to insert.
     * @param comparator Comparator to use for sorting the simplex vertices
     * from best to worst.
     */
    protected void replaceWorstPoint(PointValuePair pointValuePair,
                                     final Comparator<PointValuePair> comparator) {
        for (int i = 0; i < dimension; i++) {
            if (comparator.compare(simplex[i], pointValuePair) > 0) {
                PointValuePair tmp = simplex[i];
                simplex[i] = pointValuePair;
                pointValuePair = tmp;
            }
        }
        simplex[dimension] = pointValuePair;
    }

    /**
     * Get the points of the simplex.
     *
     * @return all the simplex points.
     */
    public PointValuePair[] getPoints() {
        final PointValuePair[] copy = new PointValuePair[simplex.length];
        System.arraycopy(simplex, 0, copy, 0, simplex.length);
        return copy;
    }

    /**
     * Get the simplex point stored at the requested {@code index}.
     *
     * @param index Location.
     * @return the point at location {@code index}.
     */
    public PointValuePair getPoint(int index) {
        if (index < 0 ||
            index >= simplex.length) {
            throw new OutOfRangeException(index, 0, simplex.length - 1);
        }
        return simplex[index];
    }

    /**
     * Store a new point at location {@code index}.
     * Note that no deep-copy of {@code point} is performed.
     *
     * @param index Location.
     * @param point New value.
     */
    protected void setPoint(int index, PointValuePair point) {
        if (index < 0 ||
            index >= simplex.length) {
            throw new OutOfRangeException(index, 0, simplex.length - 1);
        }
        simplex[index] = point;
    }

    /**
     * Replace all points.
     * Note that no deep-copy of {@code points} is performed.
     *
     * @param points New Points.
     */
    protected void setPoints(PointValuePair[] points) {
        if (points.length != simplex.length) {
            throw new DimensionMismatchException(points.length, simplex.length);
        }
        simplex = points;
    }

    /**
     * Create steps for a unit hypercube.
     *
     * @param n Dimension of the hypercube.
     * @param sideLength Length of the sides of the hypercube.
     * @return the steps.
     */
    private static double[] createHypercubeSteps(int n,
                                                 double sideLength) {
        final double[] steps = new double[n];
        for (int i = 0; i < n; i++) {
            steps[i] = sideLength;
        }
        return steps;
    }
}
