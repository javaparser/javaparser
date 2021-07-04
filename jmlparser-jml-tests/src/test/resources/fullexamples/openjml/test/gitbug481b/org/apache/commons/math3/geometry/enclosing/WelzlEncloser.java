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
package org.apache.commons.math3.geometry.enclosing;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;

/** Class implementing Emo Welzl algorithm to find the smallest enclosing ball in linear time.
 * <p>
 * The class implements the algorithm described in paper <a
 * href="http://www.inf.ethz.ch/personal/emo/PublFiles/SmallEnclDisk_LNCS555_91.pdf">Smallest
 * Enclosing Disks (Balls and Ellipsoids)</a> by Emo Welzl, Lecture Notes in Computer Science
 * 555 (1991) 359-370. The pivoting improvement published in the paper <a
 * href="http://www.inf.ethz.ch/personal/gaertner/texts/own_work/esa99_final.pdf">Fast and
 * Robust Smallest Enclosing Balls</a>, by Bernd Gärtner and further modified in
 * paper <a
 * href=http://www.idt.mdh.se/kurser/ct3340/ht12/MINICONFERENCE/FinalPapers/ircse12_submission_30.pdf">
 * Efficient Computation of Smallest Enclosing Balls in Three Dimensions</a> by Linus Källberg
 * to avoid performing local copies of data have been included.
 * </p>
 * @param <S> Space type.
 * @param <P> Point type.
 * @since 3.3
 */
public class WelzlEncloser<S extends Space, P extends Point<S>> implements Encloser<S, P> {

    /** Tolerance below which points are consider to be identical. */
    private final double tolerance;

    /** Generator for balls on support. */
    private final SupportBallGenerator<S, P> generator;

    /** Simple constructor.
     * @param tolerance below which points are consider to be identical
     * @param generator generator for balls on support
     */
    public WelzlEncloser(final double tolerance, final SupportBallGenerator<S, P> generator) {
        this.tolerance = tolerance;
        this.generator = generator;
    }

    /** {@inheritDoc} */
    public EnclosingBall<S, P> enclose(final Iterable<P> points) {

        if (points == null || !points.iterator().hasNext()) {
            // return an empty ball
            return generator.ballOnSupport(new ArrayList<P>());
        }

        // Emo Welzl algorithm with Bernd Gärtner and Linus Källberg improvements
        return pivotingBall(points);

    }

    /** Compute enclosing ball using Gärtner's pivoting heuristic.
     * @param points points to be enclosed
     * @return enclosing ball
     */
    private EnclosingBall<S, P> pivotingBall(final Iterable<P> points) {

        final P first = points.iterator().next();
        final List<P> extreme = new ArrayList<P>(first.getSpace().getDimension() + 1);
        final List<P> support = new ArrayList<P>(first.getSpace().getDimension() + 1);

        // start with only first point selected as a candidate support
        extreme.add(first);
        EnclosingBall<S, P> ball = moveToFrontBall(extreme, extreme.size(), support);

        while (true) {

            // select the point farthest to current ball
            final P farthest = selectFarthest(points, ball);

            if (ball.contains(farthest, tolerance)) {
                // we have found a ball containing all points
                return ball;
            }

            // recurse search, restricted to the small subset containing support and farthest point
            support.clear();
            support.add(farthest);
            EnclosingBall<S, P> savedBall = ball;
            ball = moveToFrontBall(extreme, extreme.size(), support);
            if (ball.getRadius() < savedBall.getRadius()) {
                // this should never happen
                throw new MathInternalError();
            }

            // it was an interesting point, move it to the front
            // according to Gärtner's heuristic
            extreme.add(0, farthest);

            // prune the least interesting points
            extreme.subList(ball.getSupportSize(), extreme.size()).clear();


        }
    }

    /** Compute enclosing ball using Welzl's move to front heuristic.
     * @param extreme subset of extreme points
     * @param nbExtreme number of extreme points to consider
     * @param support points that must belong to the ball support
     * @return enclosing ball, for the extreme subset only
     */
    private EnclosingBall<S, P> moveToFrontBall(final List<P> extreme, final int nbExtreme,
                                                final List<P> support) {

        // create a new ball on the prescribed support
        EnclosingBall<S, P> ball = generator.ballOnSupport(support);

        if (ball.getSupportSize() <= ball.getCenter().getSpace().getDimension()) {

            for (int i = 0; i < nbExtreme; ++i) {
                final P pi = extreme.get(i);
                if (!ball.contains(pi, tolerance)) {

                    // we have found an outside point,
                    // enlarge the ball by adding it to the support
                    support.add(pi);
                    ball = moveToFrontBall(extreme, i, support);
                    support.remove(support.size() - 1);

                    // it was an interesting point, move it to the front
                    // according to Welzl's heuristic
                    for (int j = i; j > 0; --j) {
                        extreme.set(j, extreme.get(j - 1));
                    }
                    extreme.set(0, pi);

                }
            }

        }

        return ball;

    }

    /** Select the point farthest to the current ball.
     * @param points points to be enclosed
     * @param ball current ball
     * @return farthest point
     */
    public P selectFarthest(final Iterable<P> points, final EnclosingBall<S, P> ball) {

        final P center = ball.getCenter();
        P farthest   = null;
        double dMax  = -1.0;

        for (final P point : points) {
            final double d = point.distance(center);
            if (d > dMax) {
                farthest = point;
                dMax     = d;
            }
        }

        return farthest;

    }

}
