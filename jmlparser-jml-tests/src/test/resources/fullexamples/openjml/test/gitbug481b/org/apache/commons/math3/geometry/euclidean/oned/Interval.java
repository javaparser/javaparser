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
package org.apache.commons.math3.geometry.euclidean.oned;

import org.apache.commons.math3.geometry.partitioning.Region.Location;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;


/** This class represents a 1D interval.
 * @see IntervalsSet
 * @since 3.0
 */
public class Interval {

    /** The lower bound of the interval. */
    private final double lower;

    /** The upper bound of the interval. */
    private final double upper;

    /** Simple constructor.
     * @param lower lower bound of the interval
     * @param upper upper bound of the interval
     */
    public Interval(final double lower, final double upper) {
        if (upper < lower) {
            throw new NumberIsTooSmallException(LocalizedFormats.ENDPOINTS_NOT_AN_INTERVAL,
                                                upper, lower, true);
        }
        this.lower = lower;
        this.upper = upper;
    }

    /** Get the lower bound of the interval.
     * @return lower bound of the interval
     * @since 3.1
     */
    public double getInf() {
        return lower;
    }

    /** Get the lower bound of the interval.
     * @return lower bound of the interval
     * @deprecated as of 3.1, replaced by {@link #getInf()}
     */
    @Deprecated
    public double getLower() {
        return getInf();
    }

    /** Get the upper bound of the interval.
     * @return upper bound of the interval
     * @since 3.1
     */
    public double getSup() {
        return upper;
    }

    /** Get the upper bound of the interval.
     * @return upper bound of the interval
     * @deprecated as of 3.1, replaced by {@link #getSup()}
     */
    @Deprecated
    public double getUpper() {
        return getSup();
    }

    /** Get the size of the interval.
     * @return size of the interval
     * @since 3.1
     */
    public double getSize() {
        return upper - lower;
    }

    /** Get the length of the interval.
     * @return length of the interval
     * @deprecated as of 3.1, replaced by {@link #getSize()}
     */
    @Deprecated
    public double getLength() {
        return getSize();
    }

    /** Get the barycenter of the interval.
     * @return barycenter of the interval
     * @since 3.1
     */
    public double getBarycenter() {
        return 0.5 * (lower + upper);
    }

    /** Get the midpoint of the interval.
     * @return midpoint of the interval
     * @deprecated as of 3.1, replaced by {@link #getBarycenter()}
     */
    @Deprecated
    public double getMidPoint() {
        return getBarycenter();
    }

    /** Check a point with respect to the interval.
     * @param point point to check
     * @param tolerance tolerance below which points are considered to
     * belong to the boundary
     * @return a code representing the point status: either {@link
     * Location#INSIDE}, {@link Location#OUTSIDE} or {@link Location#BOUNDARY}
     * @since 3.1
     */
    public Location checkPoint(final double point, final double tolerance) {
        if (point < lower - tolerance || point > upper + tolerance) {
            return Location.OUTSIDE;
        } else if (point > lower + tolerance && point < upper - tolerance) {
            return Location.INSIDE;
        } else {
            return Location.BOUNDARY;
        }
    }

}
