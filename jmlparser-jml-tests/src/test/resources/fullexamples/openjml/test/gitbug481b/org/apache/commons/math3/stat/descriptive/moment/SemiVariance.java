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

package org.apache.commons.math3.stat.descriptive.moment;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.stat.descriptive.AbstractUnivariateStatistic;
import org.apache.commons.math3.util.MathUtils;

/**
 * <p>Computes the semivariance of a set of values with respect to a given cutoff value.
 * We define the <i>downside semivariance</i> of a set of values <code>x</code>
 * against the <i>cutoff value</i> <code>cutoff</code> to be <br/>
 * <code>&Sigma; (x[i] - target)<sup>2</sup> / df</code> <br/>
 * where the sum is taken over all <code>i</code> such that <code>x[i] < cutoff</code>
 * and <code>df</code> is the length of <code>x</code> (non-bias-corrected) or
 * one less than this number (bias corrected).  The <i>upside semivariance</i>
 * is defined similarly, with the sum taken over values of <code>x</code> that
 * exceed the cutoff value.</p>
 *
 * <p>The cutoff value defaults to the mean, bias correction defaults to <code>true</code>
 * and the "variance direction" (upside or downside) defaults to downside.  The variance direction
 * and bias correction may be set using property setters or their values can provided as
 * parameters to {@link #evaluate(double[], double, Direction, boolean, int, int)}.</p>
 *
 * <p>If the input array is null, <code>evaluate</code> methods throw
 * <code>IllegalArgumentException.</code>  If the array has length 1, <code>0</code>
 * is returned, regardless of the value of the <code>cutoff.</code>
 *
 * <p><strong>Note that this class is not intended to be threadsafe.</strong> If
 * multiple threads access an instance of this class concurrently, and one or
 * more of these threads invoke property setters, external synchronization must
 * be provided to ensure correct results.</p>
 *
 * @since 2.1
 */
public class SemiVariance extends AbstractUnivariateStatistic implements Serializable {

    /**
     * The UPSIDE Direction is used to specify that the observations above the
     * cutoff point will be used to calculate SemiVariance.
     */
    public static final Direction UPSIDE_VARIANCE = Direction.UPSIDE;

    /**
     * The DOWNSIDE Direction is used to specify that the observations below
     * the cutoff point will be used to calculate SemiVariance
     */
    public static final Direction DOWNSIDE_VARIANCE = Direction.DOWNSIDE;

    /** Serializable version identifier */
    private static final long serialVersionUID = -2653430366886024994L;

    /**
     * Determines whether or not bias correction is applied when computing the
     * value of the statisic.  True means that bias is corrected.
     */
    private boolean biasCorrected = true;

    /**
     * Determines whether to calculate downside or upside SemiVariance.
     */
    private Direction varianceDirection = Direction.DOWNSIDE;

    /**
     * Constructs a SemiVariance with default (true) <code>biasCorrected</code>
     * property and default (Downside) <code>varianceDirection</code> property.
     */
    public SemiVariance() {
    }

    /**
     * Constructs a SemiVariance with the specified <code>biasCorrected</code>
     * property and default (Downside) <code>varianceDirection</code> property.
     *
     * @param biasCorrected  setting for bias correction - true means
     * bias will be corrected and is equivalent to using the argumentless
     * constructor
     */
    public SemiVariance(final boolean biasCorrected) {
        this.biasCorrected = biasCorrected;
    }


    /**
     * Constructs a SemiVariance with the specified <code>Direction</code> property
     * and default (true) <code>biasCorrected</code> property
     *
     * @param direction  setting for the direction of the SemiVariance
     * to calculate
     */
    public SemiVariance(final Direction direction) {
        this.varianceDirection = direction;
    }


    /**
     * Constructs a SemiVariance with the specified <code>isBiasCorrected</code>
     * property and the specified <code>Direction</code> property.
     *
     * @param corrected  setting for bias correction - true means
     * bias will be corrected and is equivalent to using the argumentless
     * constructor
     *
     * @param direction  setting for the direction of the SemiVariance
     * to calculate
     */
    public SemiVariance(final boolean corrected, final Direction direction) {
        this.biasCorrected = corrected;
        this.varianceDirection = direction;
    }


    /**
     * Copy constructor, creates a new {@code SemiVariance} identical
     * to the {@code original}
     *
     * @param original the {@code SemiVariance} instance to copy
     * @throws NullArgumentException  if original is null
     */
    public SemiVariance(final SemiVariance original) throws NullArgumentException {
        copy(original, this);
    }


    /**
     * {@inheritDoc}
     */
    @Override
    public SemiVariance copy() {
        SemiVariance result = new SemiVariance();
        // No try-catch or advertised exception because args are guaranteed non-null
        copy(this, result);
        return result;
    }


    /**
     * Copies source to dest.
     * <p>Neither source nor dest can be null.</p>
     *
     * @param source SemiVariance to copy
     * @param dest SemiVariance to copy to
     * @throws NullArgumentException if either source or dest is null
     */
    public static void copy(final SemiVariance source, SemiVariance dest)
        throws NullArgumentException {
        MathUtils.checkNotNull(source);
        MathUtils.checkNotNull(dest);
        dest.setData(source.getDataRef());
        dest.biasCorrected = source.biasCorrected;
        dest.varianceDirection = source.varianceDirection;
    }

    /**
      * <p>Returns the {@link SemiVariance} of the designated values against the mean, using
      * instance properties varianceDirection and biasCorrection.</p>
      *
      * <p>Returns <code>NaN</code> if the array is empty and throws
      * <code>IllegalArgumentException</code> if the array is null.</p>
      *
      * @param values the input array
      * @param start index of the first array element to include
      * @param length the number of elements to include
      * @return the SemiVariance
      * @throws MathIllegalArgumentException if the parameters are not valid
      *
      */
      @Override
      public double evaluate(final double[] values, final int start, final int length)
      throws MathIllegalArgumentException {
        double m = (new Mean()).evaluate(values, start, length);
        return evaluate(values, m, varianceDirection, biasCorrected, 0, values.length);
      }


      /**
       * This method calculates {@link SemiVariance} for the entire array against the mean, using
       * the current value of the biasCorrection instance property.
       *
       * @param values the input array
       * @param direction the {@link Direction} of the semivariance
       * @return the SemiVariance
       * @throws MathIllegalArgumentException if values is null
       *
       */
      public double evaluate(final double[] values, Direction direction)
      throws MathIllegalArgumentException {
          double m = (new Mean()).evaluate(values);
          return evaluate (values, m, direction, biasCorrected, 0, values.length);
      }

      /**
       * <p>Returns the {@link SemiVariance} of the designated values against the cutoff, using
       * instance properties variancDirection and biasCorrection.</p>
       *
       * <p>Returns <code>NaN</code> if the array is empty and throws
       * <code>MathIllegalArgumentException</code> if the array is null.</p>
       *
       * @param values the input array
       * @param cutoff the reference point
       * @return the SemiVariance
       * @throws MathIllegalArgumentException if values is null
       */
      public double evaluate(final double[] values, final double cutoff)
      throws MathIllegalArgumentException {
          return evaluate(values, cutoff, varianceDirection, biasCorrected, 0, values.length);
      }

      /**
       * <p>Returns the {@link SemiVariance} of the designated values against the cutoff in the
       * given direction, using the current value of the biasCorrection instance property.</p>
       *
       * <p>Returns <code>NaN</code> if the array is empty and throws
       * <code>MathIllegalArgumentException</code> if the array is null.</p>
       *
       * @param values the input array
       * @param cutoff the reference point
       * @param direction the {@link Direction} of the semivariance
       * @return the SemiVariance
       * @throws MathIllegalArgumentException if values is null
       */
      public double evaluate(final double[] values, final double cutoff, final Direction direction)
      throws MathIllegalArgumentException {
          return evaluate(values, cutoff, direction, biasCorrected, 0, values.length);
      }


     /**
      * <p>Returns the {@link SemiVariance} of the designated values against the cutoff
      * in the given direction with the provided bias correction.</p>
      *
      * <p>Returns <code>NaN</code> if the array is empty and throws
      * <code>IllegalArgumentException</code> if the array is null.</p>
      *
      * @param values the input array
      * @param cutoff the reference point
      * @param direction the {@link Direction} of the semivariance
      * @param corrected the BiasCorrection flag
      * @param start index of the first array element to include
      * @param length the number of elements to include
      * @return the SemiVariance
      * @throws MathIllegalArgumentException if the parameters are not valid
      *
      */
    public double evaluate (final double[] values, final double cutoff, final Direction direction,
            final boolean corrected, final int start, final int length) throws MathIllegalArgumentException {

        test(values, start, length);
        if (values.length == 0) {
            return Double.NaN;
        } else {
            if (values.length == 1) {
                return 0.0;
            } else {
                final boolean booleanDirection = direction.getDirection();

                double dev = 0.0;
                double sumsq = 0.0;
                for (int i = start; i < length; i++) {
                    if ((values[i] > cutoff) == booleanDirection) {
                       dev = values[i] - cutoff;
                       sumsq += dev * dev;
                    }
                }

                if (corrected) {
                    return sumsq / (length - 1.0);
                } else {
                    return sumsq / length;
                }
            }
        }
    }

    /**
     * Returns true iff biasCorrected property is set to true.
     *
     * @return the value of biasCorrected.
     */
    public boolean isBiasCorrected() {
        return biasCorrected;
    }

    /**
     * Sets the biasCorrected property.
     *
     * @param biasCorrected new biasCorrected property value
     */
    public void setBiasCorrected(boolean biasCorrected) {
        this.biasCorrected = biasCorrected;
    }

    /**
     * Returns the varianceDirection property.
     *
     * @return the varianceDirection
     */
    public Direction getVarianceDirection () {
        return varianceDirection;
    }

    /**
     * Sets the variance direction
     *
     * @param varianceDirection the direction of the semivariance
     */
    public void setVarianceDirection(Direction varianceDirection) {
        this.varianceDirection = varianceDirection;
    }

    /**
     * The direction of the semivariance - either upside or downside. The direction
     * is represented by boolean, with true corresponding to UPSIDE semivariance.
     */
    public enum Direction {
        /**
         * The UPSIDE Direction is used to specify that the observations above the
         * cutoff point will be used to calculate SemiVariance
         */
        UPSIDE (true),

        /**
         * The DOWNSIDE Direction is used to specify that the observations below
         * the cutoff point will be used to calculate SemiVariance
         */
        DOWNSIDE (false);

        /**
         *   boolean value  UPSIDE <-> true
         */
        private boolean direction;

        /**
         * Create a Direction with the given value.
         *
         * @param b boolean value representing the Direction. True corresponds to UPSIDE.
         */
        Direction (boolean b) {
            direction = b;
        }

        /**
         * Returns the value of this Direction. True corresponds to UPSIDE.
         *
         * @return true if direction is UPSIDE; false otherwise
         */
        boolean getDirection () {
            return direction;
        }
    }
}
