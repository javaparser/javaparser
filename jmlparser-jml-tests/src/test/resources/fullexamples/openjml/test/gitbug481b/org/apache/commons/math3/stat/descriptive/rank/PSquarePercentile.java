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
package org.apache.commons.math3.stat.descriptive.rank;

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.Serializable;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import org.apache.commons.math3.analysis.UnivariateFunction;
import org.apache.commons.math3.analysis.interpolation.LinearInterpolator;
import org.apache.commons.math3.analysis.interpolation.NevilleInterpolator;
import org.apache.commons.math3.analysis.interpolation.UnivariateInterpolator;
import org.apache.commons.math3.exception.InsufficientDataException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.stat.descriptive.AbstractStorelessUnivariateStatistic;
import org.apache.commons.math3.stat.descriptive.StorelessUnivariateStatistic;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;
import org.apache.commons.math3.util.Precision;

/**
 * A {@link StorelessUnivariateStatistic} estimating percentiles using the
 * <ahref=http://www.cs.wustl.edu/~jain/papers/ftp/psqr.pdf>P<SUP>2</SUP></a>
 * Algorithm as explained by <a href=http://www.cse.wustl.edu/~jain/>Raj
 * Jain</a> and Imrich Chlamtac in
 * <a href=http://www.cse.wustl.edu/~jain/papers/psqr.htm>P<SUP>2</SUP> Algorithm
 * for Dynamic Calculation of Quantiles and Histogram Without Storing
 * Observations</a>.
 * <p>
 * Note: This implementation is not synchronized and produces an approximate
 * result. For small samples, where data can be stored and processed in memory,
 * {@link Percentile} should be used.</p>
 *
 */
public class PSquarePercentile extends AbstractStorelessUnivariateStatistic
        implements StorelessUnivariateStatistic, Serializable {

    /**
     * The maximum array size used for psquare algorithm
     */
    private static final int PSQUARE_CONSTANT = 5;

    /**
     * A Default quantile needed in case if user prefers to use default no
     * argument constructor.
     */
    private static final double DEFAULT_QUANTILE_DESIRED = 50d;

    /**
     * Serial ID
     */
    private static final long serialVersionUID = 2283912083175715479L;

    /**
     * A decimal formatter for print convenience
     */
    private static final DecimalFormat DECIMAL_FORMAT = new DecimalFormat(
            "00.00");

    /**
     * Initial list of 5 numbers corresponding to 5 markers. <b>NOTE:</b>watch
     * out for the add methods that are overloaded
     */
    private final List<Double> initialFive = new FixedCapacityList<Double>(
            PSQUARE_CONSTANT);

    /**
     * The quantile needed should be in range of 0-1. The constructor
     * {@link #PSquarePercentile(double)} ensures that passed in percentile is
     * divided by 100.
     */
    private final double quantile;

    /**
     * lastObservation is the last observation value/input sample. No need to
     * serialize
     */
    private transient double lastObservation;

    /**
     * Markers is the marker collection object which comes to effect
     * only after 5 values are inserted
     */
    private PSquareMarkers markers = null;

    /**
     * Computed p value (i,e percentile value of data set hither to received)
     */
    private double pValue = Double.NaN;

    /**
     * Counter to count the values/observations accepted into this data set
     */
    private long countOfObservations;

    /**
     * Constructs a PSquarePercentile with the specific percentile value.
     * @param p the percentile
     * @throws OutOfRangeException  if p is not greater than 0 and less
     * than or equal to 100
     */
    public PSquarePercentile(final double p) {
        if (p > 100 || p < 0) {
            throw new OutOfRangeException(LocalizedFormats.OUT_OF_RANGE,
                    p, 0, 100);
        }
        this.quantile = p / 100d;// always set it within (0,1]
    }

    /**
     * Default constructor that assumes a {@link #DEFAULT_QUANTILE_DESIRED
     * default quantile} needed
     */
    PSquarePercentile() {
        this(DEFAULT_QUANTILE_DESIRED);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        double result = getResult();
        result = Double.isNaN(result) ? 37 : result;
        final double markersHash = markers == null ? 0 : markers.hashCode();
        final double[] toHash = {result, quantile, markersHash, countOfObservations};
        return Arrays.hashCode(toHash);
    }

    /**
     * Returns true iff {@code o} is a {@code PSquarePercentile} returning the
     * same values as this for {@code getResult()} and {@code getN()} and also
     * having equal markers
     *
     * @param o object to compare
     * @return true if {@code o} is a {@code PSquarePercentile} with
     * equivalent internal state
     */
    @Override
    public boolean equals(Object o) {
        boolean result = false;
        if (this == o) {
            result = true;
        } else if (o != null && o instanceof PSquarePercentile) {
            PSquarePercentile that = (PSquarePercentile) o;
            boolean isNotNull = markers != null && that.markers != null;
            boolean isNull = markers == null && that.markers == null;
            result = isNotNull ? markers.equals(that.markers) : isNull;
            // markers as in the case of first
            // five observations
            result = result && getN() == that.getN();
        }
        return result;
    }

    /**
     * {@inheritDoc}The internal state updated due to the new value in this
     * context is basically of the marker positions and computation of the
     * approximate quantile.
     *
     * @param observation the observation currently being added.
     */
    @Override
    public void increment(final double observation) {
        // Increment counter
        countOfObservations++;

        // Store last observation
        this.lastObservation = observation;

        // 0. Use Brute force for <5
        if (markers == null) {
            if (initialFive.add(observation)) {
                Collections.sort(initialFive);
                pValue =
                        initialFive
                                .get((int) (quantile * (initialFive.size() - 1)));
                return;
            }
            // 1. Initialize once after 5th observation
            markers = newMarkers(initialFive, quantile);
        }
        // 2. process a Data Point and return pValue
        pValue = markers.processDataPoint(observation);
    }

    /**
     * Returns a string containing the last observation, the current estimate
     * of the quantile and all markers.
     *
     * @return string representation of state data
     */
    @Override
    public String toString() {

        if (markers == null) {
            return String.format("obs=%s pValue=%s",
                    DECIMAL_FORMAT.format(lastObservation),
                    DECIMAL_FORMAT.format(pValue));
        } else {
            return String.format("obs=%s markers=%s",
                    DECIMAL_FORMAT.format(lastObservation), markers.toString());
        }
    }

    /**
     * {@inheritDoc}
     */
    public long getN() {
        return countOfObservations;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public StorelessUnivariateStatistic copy() {
        // multiply quantile by 100 now as anyway constructor divides it by 100
        PSquarePercentile copy = new PSquarePercentile(100d * quantile);

        if (markers != null) {
            copy.markers = (PSquareMarkers) markers.clone();
        }
        copy.countOfObservations = countOfObservations;
        copy.pValue = pValue;
        copy.initialFive.clear();
        copy.initialFive.addAll(initialFive);
        return copy;
    }

    /**
     * Returns the quantile estimated by this statistic in the range [0.0-1.0]
     *
     * @return quantile estimated by {@link #getResult()}
     */
    public double quantile() {
        return quantile;
    }

    /**
     * {@inheritDoc}. This basically clears all the markers, the
     * initialFive list and sets countOfObservations to 0.
     */
    @Override
    public void clear() {
        markers = null;
        initialFive.clear();
        countOfObservations = 0L;
        pValue = Double.NaN;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public double getResult() {
        if (Double.compare(quantile, 1d) == 0) {
            pValue = maximum();
        } else if (Double.compare(quantile, 0d) == 0) {
            pValue = minimum();
        }
        return pValue;
    }

    /**
     * @return maximum in the data set added to this statistic
     */
    private double maximum() {
        double val = Double.NaN;
        if (markers != null) {
            val = markers.height(PSQUARE_CONSTANT);
        } else if (!initialFive.isEmpty()) {
            val = initialFive.get(initialFive.size() - 1);
        }
        return val;
    }

    /**
     * @return minimum in the data set added to this statistic
     */
    private double minimum() {
        double val = Double.NaN;
        if (markers != null) {
            val = markers.height(1);
        } else if (!initialFive.isEmpty()) {
            val = initialFive.get(0);
        }
        return val;
    }

    /**
     * Markers is an encapsulation of the five markers/buckets as indicated in
     * the original works.
     */
    private static class Markers implements PSquareMarkers, Serializable {
        /**
         * Serial version id
         */
        private static final long serialVersionUID = 1L;

        /** Low marker index */
        private static final int LOW = 2;

        /** High marker index */
        private static final int HIGH = 4;

        /**
         * Array of 5+1 Markers (The first marker is dummy just so we
         * can match the rest of indexes [1-5] indicated in the original works
         * which follows unit based index)
         */
        private final Marker[] markerArray;

        /**
         * Kth cell belonging to [1-5] of the markerArray. No need for
         * this to be serialized
         */
        private transient int k = -1;

        /**
         * Constructor
         *
         * @param theMarkerArray marker array to be used
         */
        private Markers(final Marker[] theMarkerArray) {
            MathUtils.checkNotNull(theMarkerArray);
            markerArray = theMarkerArray;
            for (int i = 1; i < PSQUARE_CONSTANT; i++) {
                markerArray[i].previous(markerArray[i - 1])
                        .next(markerArray[i + 1]).index(i);
            }
            markerArray[0].previous(markerArray[0]).next(markerArray[1])
                    .index(0);
            markerArray[5].previous(markerArray[4]).next(markerArray[5])
                    .index(5);
        }

        /**
         * Constructor
         *
         * @param initialFive elements required to build Marker
         * @param p quantile required to be computed
         */
        private Markers(final List<Double> initialFive, final double p) {
            this(createMarkerArray(initialFive, p));
        }

        /**
         * Creates a marker array using initial five elements and a quantile
         *
         * @param initialFive list of initial five elements
         * @param p the pth quantile
         * @return Marker array
         */
        private static Marker[] createMarkerArray(
                final List<Double> initialFive, final double p) {
            final int countObserved =
                    initialFive == null ? -1 : initialFive.size();
            if (countObserved < PSQUARE_CONSTANT) {
                throw new InsufficientDataException(
                        LocalizedFormats.INSUFFICIENT_OBSERVED_POINTS_IN_SAMPLE,
                        countObserved, PSQUARE_CONSTANT);
            }
            Collections.sort(initialFive);
            return new Marker[] {
                    new Marker(),// Null Marker
                    new Marker(initialFive.get(0), 1, 0, 1),
                    new Marker(initialFive.get(1), 1 + 2 * p, p / 2, 2),
                    new Marker(initialFive.get(2), 1 + 4 * p, p, 3),
                    new Marker(initialFive.get(3), 3 + 2 * p, (1 + p) / 2, 4),
                    new Marker(initialFive.get(4), 5, 1, 5) };
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public int hashCode() {
            return Arrays.deepHashCode(markerArray);
        }

        /**
         * {@inheritDoc}.This equals method basically checks for marker array to
         * be deep equals.
         *
         * @param o is the other object
         * @return true if the object compares with this object are equivalent
         */
        @Override
        public boolean equals(Object o) {
            boolean result = false;
            if (this == o) {
                result = true;
            } else if (o != null && o instanceof Markers) {
                Markers that = (Markers) o;
                result = Arrays.deepEquals(markerArray, that.markerArray);
            }
            return result;
        }

        /**
         * Process a data point
         *
         * @param inputDataPoint is the data point passed
         * @return computed percentile
         */
        public double processDataPoint(final double inputDataPoint) {

            // 1. Find cell and update minima and maxima
            final int kthCell = findCellAndUpdateMinMax(inputDataPoint);

            // 2. Increment positions
            incrementPositions(1, kthCell + 1, 5);

            // 2a. Update desired position with increments
            updateDesiredPositions();

            // 3. Adjust heights of m[2-4] if necessary
            adjustHeightsOfMarkers();

            // 4. Return percentile
            return getPercentileValue();
        }

        /**
         * Returns the percentile computed thus far.
         *
         * @return height of mid point marker
         */
        public double getPercentileValue() {
            return height(3);
        }

        /**
         * Finds the cell where the input observation / value fits.
         *
         * @param observation the input value to be checked for
         * @return kth cell (of the markers ranging from 1-5) where observed
         *         sample fits
         */
        private int findCellAndUpdateMinMax(final double observation) {
            k = -1;
            if (observation < height(1)) {
                markerArray[1].markerHeight = observation;
                k = 1;
            } else if (observation < height(2)) {
                k = 1;
            } else if (observation < height(3)) {
                k = 2;
            } else if (observation < height(4)) {
                k = 3;
            } else if (observation <= height(5)) {
                k = 4;
            } else {
                markerArray[5].markerHeight = observation;
                k = 4;
            }
            return k;
        }

        /**
         * Adjust marker heights by setting quantile estimates to middle markers.
         */
        private void adjustHeightsOfMarkers() {
            for (int i = LOW; i <= HIGH; i++) {
                estimate(i);
            }
        }

        /**
         * {@inheritDoc}
         */
        public double estimate(final int index) {
            if (index < LOW || index > HIGH) {
                throw new OutOfRangeException(index, LOW, HIGH);
            }
            return markerArray[index].estimate();
        }

        /**
         * Increment positions by d. Refer to algorithm paper for the
         * definition of d.
         *
         * @param d The increment value for the position
         * @param startIndex start index of the marker array
         * @param endIndex end index of the marker array
         */
        private void incrementPositions(final int d, final int startIndex,
                final int endIndex) {
            for (int i = startIndex; i <= endIndex; i++) {
                markerArray[i].incrementPosition(d);
            }
        }

        /**
         * Desired positions incremented by bucket width. The bucket width is
         * basically the desired increments.
         */
        private void updateDesiredPositions() {
            for (int i = 1; i < markerArray.length; i++) {
                markerArray[i].updateDesiredPosition();
            }
        }

        /**
         * Sets previous and next markers after default read is done.
         *
         * @param anInputStream the input stream to be deserialized
         * @throws ClassNotFoundException thrown when a desired class not found
         * @throws IOException thrown due to any io errors
         */
        private void readObject(ObjectInputStream anInputStream)
                throws ClassNotFoundException, IOException {
            // always perform the default de-serialization first
            anInputStream.defaultReadObject();
            // Build links
            for (int i = 1; i < PSQUARE_CONSTANT; i++) {
                markerArray[i].previous(markerArray[i - 1])
                        .next(markerArray[i + 1]).index(i);
            }
            markerArray[0].previous(markerArray[0]).next(markerArray[1])
                    .index(0);
            markerArray[5].previous(markerArray[4]).next(markerArray[5])
                    .index(5);
        }

        /**
         * Return marker height given index
         *
         * @param markerIndex index of marker within (1,6)
         * @return marker height
         */
        public double height(final int markerIndex) {
            if (markerIndex >= markerArray.length || markerIndex <= 0) {
                throw new OutOfRangeException(markerIndex, 1,
                        markerArray.length);
            }
            return markerArray[markerIndex].markerHeight;
        }

        /**
         * {@inheritDoc}.Clone Markers
         *
         * @return cloned object
         */
        @Override
        public Object clone() {
            return new Markers(new Marker[] { new Marker(),
                    (Marker) markerArray[1].clone(),
                    (Marker) markerArray[2].clone(),
                    (Marker) markerArray[3].clone(),
                    (Marker) markerArray[4].clone(),
                    (Marker) markerArray[5].clone() });

        }

        /**
         * Returns string representation of the Marker array.
         *
         * @return Markers as a string
         */
        @Override
        public String toString() {
            return String.format("m1=[%s],m2=[%s],m3=[%s],m4=[%s],m5=[%s]",
                    markerArray[1].toString(), markerArray[2].toString(),
                    markerArray[3].toString(), markerArray[4].toString(),
                    markerArray[5].toString());
        }

    }

    /**
     * The class modeling the attributes of the marker of the P-square algorithm
     */
    private static class Marker implements Serializable, Cloneable {

        /**
         * Serial Version ID
         */
        private static final long serialVersionUID = -3575879478288538431L;

        /**
         * The marker index which is just a serial number for the marker in the
         * marker array of 5+1.
         */
        private int index;

        /**
         * The integral marker position. Refer to the variable n in the original
         * works.
         */
        private double intMarkerPosition;

        /**
         * Desired marker position. Refer to the variable n' in the original
         * works.
         */
        private double desiredMarkerPosition;

        /**
         * Marker height or the quantile. Refer to the variable q in the
         * original works.
         */
        private double markerHeight;

        /**
         * Desired marker increment. Refer to the variable dn' in the original
         * works.
         */
        private double desiredMarkerIncrement;

        /**
         * Next and previous markers for easy linked navigation in loops. this
         * is not serialized as they can be rebuilt during deserialization.
         */
        private transient Marker next;

        /**
         * The previous marker links
         */
        private transient Marker previous;

        /**
         * Nonlinear interpolator
         */
        private final UnivariateInterpolator nonLinear =
                new NevilleInterpolator();

        /**
         * Linear interpolator which is not serializable
         */
        private transient UnivariateInterpolator linear =
                new LinearInterpolator();

        /**
         * Default constructor
         */
        private Marker() {
            this.next = this.previous = this;
        }

        /**
         * Constructor of the marker with parameters
         *
         * @param heightOfMarker represent the quantile value
         * @param makerPositionDesired represent the desired marker position
         * @param markerPositionIncrement represent increments for position
         * @param markerPositionNumber represent the position number of marker
         */
        private Marker(double heightOfMarker, double makerPositionDesired,
                double markerPositionIncrement, double markerPositionNumber) {
            this();
            this.markerHeight = heightOfMarker;
            this.desiredMarkerPosition = makerPositionDesired;
            this.desiredMarkerIncrement = markerPositionIncrement;
            this.intMarkerPosition = markerPositionNumber;
        }

        /**
         * Sets the previous marker.
         *
         * @param previousMarker the previous marker to the current marker in
         *            the array of markers
         * @return this instance
         */
        private Marker previous(final Marker previousMarker) {
            MathUtils.checkNotNull(previousMarker);
            this.previous = previousMarker;
            return this;
        }

        /**
         * Sets the next marker.
         *
         * @param nextMarker the next marker to the current marker in the array
         *            of markers
         * @return this instance
         */
        private Marker next(final Marker nextMarker) {
            MathUtils.checkNotNull(nextMarker);
            this.next = nextMarker;
            return this;
        }

        /**
         * Sets the index of the marker.
         *
         * @param indexOfMarker the array index of the marker in marker array
         * @return this instance
         */
        private Marker index(final int indexOfMarker) {
            this.index = indexOfMarker;
            return this;
        }

        /**
         * Update desired Position with increment.
         */
        private void updateDesiredPosition() {
            desiredMarkerPosition += desiredMarkerIncrement;
        }

        /**
         * Increment Position by d.
         *
         * @param d a delta value to increment
         */
        private void incrementPosition(final int d) {
            intMarkerPosition += d;
        }

        /**
         * Difference between desired and actual position
         *
         * @return difference between desired and actual position
         */
        private double difference() {
            return desiredMarkerPosition - intMarkerPosition;
        }

        /**
         * Estimate the quantile for the current marker.
         *
         * @return estimated quantile
         */
        private double estimate() {
            final double di = difference();
            final boolean isNextHigher =
                    next.intMarkerPosition - intMarkerPosition > 1;
            final boolean isPreviousLower =
                    previous.intMarkerPosition - intMarkerPosition < -1;

            if (di >= 1 && isNextHigher || di <= -1 && isPreviousLower) {
                final int d = di >= 0 ? 1 : -1;
                final double[] xval =
                        new double[] { previous.intMarkerPosition,
                                intMarkerPosition, next.intMarkerPosition };
                final double[] yval =
                        new double[] { previous.markerHeight, markerHeight,
                                next.markerHeight };
                final double xD = intMarkerPosition + d;

                UnivariateFunction univariateFunction =
                        nonLinear.interpolate(xval, yval);
                markerHeight = univariateFunction.value(xD);

                // If parabolic estimate is bad then turn linear
                if (isEstimateBad(yval, markerHeight)) {
                    int delta = xD - xval[1] > 0 ? 1 : -1;
                    final double[] xBad =
                            new double[] { xval[1], xval[1 + delta] };
                    final double[] yBad =
                            new double[] { yval[1], yval[1 + delta] };
                    MathArrays.sortInPlace(xBad, yBad);// since d can be +/- 1
                    univariateFunction = linear.interpolate(xBad, yBad);
                    markerHeight = univariateFunction.value(xD);
                }
                incrementPosition(d);
            }
            return markerHeight;
        }

        /**
         * Check if parabolic/nonlinear estimate is bad by checking if the
         * ordinate found is beyond the y[0] and y[2].
         *
         * @param y the array to get the bounds
         * @param yD the estimate
         * @return true if yD is a bad estimate
         */
        private boolean isEstimateBad(final double[] y, final double yD) {
            return yD <= y[0] || yD >= y[2];
        }

        /**
         * {@inheritDoc}<i>This equals method checks for marker attributes and
         * as well checks if navigation pointers (next and previous) are the same
         * between this and passed in object</i>
         *
         * @param o Other object
         * @return true if this equals passed in other object o
         */
        @Override
        public boolean equals(Object o) {
            boolean result = false;
            if (this == o) {
                result = true;
            } else if (o != null && o instanceof Marker) {
                Marker that = (Marker) o;

                result = Double.compare(markerHeight, that.markerHeight) == 0;
                result =
                        result &&
                                Double.compare(intMarkerPosition,
                                        that.intMarkerPosition) == 0;
                result =
                        result &&
                                Double.compare(desiredMarkerPosition,
                                        that.desiredMarkerPosition) == 0;
                result =
                        result &&
                                Double.compare(desiredMarkerIncrement,
                                        that.desiredMarkerIncrement) == 0;

                result = result && next.index == that.next.index;
                result = result && previous.index == that.previous.index;
            }
            return result;
        }

        /** {@inheritDoc} */
        @Override
        public int hashCode() {
            return Arrays.hashCode(new double[] {markerHeight, intMarkerPosition,
                desiredMarkerIncrement, desiredMarkerPosition, previous.index, next.index});
        }

        /**
         * Read Object to deserialize.
         *
         * @param anInstream Stream Object data
         * @throws IOException thrown for IO Errors
         * @throws ClassNotFoundException thrown for class not being found
         */
        private void readObject(ObjectInputStream anInstream)
                throws ClassNotFoundException, IOException {
            anInstream.defaultReadObject();
            previous=next=this;
            linear = new LinearInterpolator();
        }

        /**
         * Clone this instance.
         *
         * @return cloned marker
         */
        @Override
        public Object clone() {
            return new Marker(markerHeight, desiredMarkerPosition,
                    desiredMarkerIncrement, intMarkerPosition);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public String toString() {
            return String.format(
                    "index=%.0f,n=%.0f,np=%.2f,q=%.2f,dn=%.2f,prev=%d,next=%d",
                    (double) index, Precision.round(intMarkerPosition, 0),
                    Precision.round(desiredMarkerPosition, 2),
                    Precision.round(markerHeight, 2),
                    Precision.round(desiredMarkerIncrement, 2), previous.index,
                    next.index);
        }
    }

    /**
     * A simple fixed capacity list that has an upper bound to growth.
     * Once its capacity is reached, {@code add} is a no-op, returning
     * {@code false}.
     *
     * @param <E>
     */
    private static class FixedCapacityList<E> extends ArrayList<E> implements
            Serializable {
        /**
         * Serialization Version Id
         */
        private static final long serialVersionUID = 2283952083075725479L;
        /**
         * Capacity of the list
         */
        private final int capacity;

        /**
         * This constructor constructs the list with given capacity and as well
         * as stores the capacity
         *
         * @param fixedCapacity the capacity to be fixed for this list
         */
        FixedCapacityList(final int fixedCapacity) {
            super(fixedCapacity);
            this.capacity = fixedCapacity;
        }

        /**
         * {@inheritDoc} In addition it checks if the {@link #size()} returns a
         * size that is within capacity and if true it adds; otherwise the list
         * contents are unchanged and {@code false} is returned.
         *
         * @return true if addition is successful and false otherwise
         */
        @Override
        public boolean add(final E e) {
            return size() < capacity ? super.add(e) : false;
        }

        /**
         * {@inheritDoc} In addition it checks if the sum of Collection size and
         * this instance's {@link #size()} returns a value that is within
         * capacity and if true it adds the collection; otherwise the list
         * contents are unchanged and {@code false} is returned.
         *
         * @return true if addition is successful and false otherwise
         */
        @Override
        public boolean addAll(Collection<? extends E> collection) {
            boolean isCollectionLess =
                    collection != null &&
                            collection.size() + size() <= capacity;
            return isCollectionLess ? super.addAll(collection) : false;
        }
    }

    /**
     * A creation method to build Markers
     *
     * @param initialFive list of initial five elements
     * @param p the quantile desired
     * @return an instance of PSquareMarkers
     */
    public static PSquareMarkers newMarkers(final List<Double> initialFive,
            final double p) {
        return new Markers(initialFive, p);
    }

    /**
     * An interface that encapsulates abstractions of the
     * P-square algorithm markers as is explained in the original works. This
     * interface is exposed with protected access to help in testability.
     */
    protected interface PSquareMarkers extends Cloneable {
        /**
         * Returns Percentile value computed thus far.
         *
         * @return percentile
         */
        double getPercentileValue();

        /**
         * A clone function to clone the current instance. It's created as an
         * interface method as well for convenience though Cloneable is just a
         * marker interface.
         *
         * @return clone of this instance
         */
        Object clone();

        /**
         * Returns the marker height (or percentile) of a given marker index.
         *
         * @param markerIndex is the index of marker in the marker array
         * @return percentile value of the marker index passed
         * @throws OutOfRangeException in case the index is not within [1-5]
         */
        double height(final int markerIndex);

        /**
         * Process a data point by moving the marker heights based on estimator.
         *
         * @param inputDataPoint is the data point passed
         * @return computed percentile
         */
        double processDataPoint(final double inputDataPoint);

        /**
         * An Estimate of the percentile value of a given Marker
         *
         * @param index the marker's index in the array of markers
         * @return percentile estimate
         * @throws OutOfRangeException in case if index is not within [1-5]
         */
        double estimate(final int index);
    }
}
