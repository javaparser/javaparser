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
package org.apache.commons.math3.geometry.spherical.twod;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.geometry.euclidean.threed.Vector3D;
import org.apache.commons.math3.geometry.partitioning.BSPTree;
import org.apache.commons.math3.geometry.partitioning.BSPTreeVisitor;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathUtils;

/** Visitor computing geometrical properties.
 * @since 3.3
 */
class PropertiesComputer implements BSPTreeVisitor<Sphere2D> {

    /** Tolerance below which points are consider to be identical. */
    private final double tolerance;

    /** Summed area. */
    private double summedArea;

    /** Summed barycenter. */
    private Vector3D summedBarycenter;

    /** List of points strictly inside convex cells. */
    private final List<Vector3D> convexCellsInsidePoints;

    /** Simple constructor.
     * @param tolerance below which points are consider to be identical
     */
    PropertiesComputer(final double tolerance) {
        this.tolerance              = tolerance;
        this.summedArea             = 0;
        this.summedBarycenter       = Vector3D.ZERO;
        this.convexCellsInsidePoints = new ArrayList<Vector3D>();
    }

    /** {@inheritDoc} */
    public Order visitOrder(final BSPTree<Sphere2D> node) {
        return Order.MINUS_SUB_PLUS;
    }

    /** {@inheritDoc} */
    public void visitInternalNode(final BSPTree<Sphere2D> node) {
        // nothing to do here
    }

    /** {@inheritDoc} */
    public void visitLeafNode(final BSPTree<Sphere2D> node) {
        if ((Boolean) node.getAttribute()) {

            // transform this inside leaf cell into a simple convex polygon
            final SphericalPolygonsSet convex =
                    new SphericalPolygonsSet(node.pruneAroundConvexCell(Boolean.TRUE,
                                                                        Boolean.FALSE,
                                                                        null),
                                             tolerance);

            // extract the start of the single loop boundary of the convex cell
            final List<Vertex> boundary = convex.getBoundaryLoops();
            if (boundary.size() != 1) {
                // this should never happen
                throw new MathInternalError();
            }

            // compute the geometrical properties of the convex cell
            final double area  = convexCellArea(boundary.get(0));
            final Vector3D barycenter = convexCellBarycenter(boundary.get(0));
            convexCellsInsidePoints.add(barycenter);

            // add the cell contribution to the global properties
            summedArea      += area;
            summedBarycenter = new Vector3D(1, summedBarycenter, area, barycenter);

        }
    }

    /** Compute convex cell area.
     * @param start start vertex of the convex cell boundary
     * @return area
     */
    private double convexCellArea(final Vertex start) {

        int n = 0;
        double sum = 0;

        // loop around the cell
        for (Edge e = start.getOutgoing(); n == 0 || e.getStart() != start; e = e.getEnd().getOutgoing()) {

            // find path interior angle at vertex
            final Vector3D previousPole = e.getCircle().getPole();
            final Vector3D nextPole     = e.getEnd().getOutgoing().getCircle().getPole();
            final Vector3D point        = e.getEnd().getLocation().getVector();
            double alpha = FastMath.atan2(Vector3D.dotProduct(nextPole, Vector3D.crossProduct(point, previousPole)),
                                          -Vector3D.dotProduct(nextPole, previousPole));
            if (alpha < 0) {
                alpha += MathUtils.TWO_PI;
            }
            sum += alpha;
            n++;
        }

        // compute area using extended Girard theorem
        // see Spherical Trigonometry: For the Use of Colleges and Schools by I. Todhunter
        // article 99 in chapter VIII Area Of a Spherical Triangle. Spherical Excess.
        // book available from project Gutenberg at http://www.gutenberg.org/ebooks/19770
        return sum - (n - 2) * FastMath.PI;

    }

    /** Compute convex cell barycenter.
     * @param start start vertex of the convex cell boundary
     * @return barycenter
     */
    private Vector3D convexCellBarycenter(final Vertex start) {

        int n = 0;
        Vector3D sumB = Vector3D.ZERO;

        // loop around the cell
        for (Edge e = start.getOutgoing(); n == 0 || e.getStart() != start; e = e.getEnd().getOutgoing()) {
            sumB = new Vector3D(1, sumB, e.getLength(), e.getCircle().getPole());
            n++;
        }

        return sumB.normalize();

    }

    /** Get the area.
     * @return area
     */
    public double getArea() {
        return summedArea;
    }

    /** Get the barycenter.
     * @return barycenter
     */
    public S2Point getBarycenter() {
        if (summedBarycenter.getNormSq() == 0) {
            return S2Point.NaN;
        } else {
            return new S2Point(summedBarycenter);
        }
    }

    /** Get the points strictly inside convex cells.
     * @return points strictly inside convex cells
     */
    public List<Vector3D> getConvexCellsInsidePoints() {
        return convexCellsInsidePoints;
    }

}
