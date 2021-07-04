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

package org.apache.commons.math3.ode;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.ode.sampling.StepHandler;
import org.apache.commons.math3.ode.sampling.StepInterpolator;
import org.apache.commons.math3.util.FastMath;

/**
 * This class stores all information provided by an ODE integrator
 * during the integration process and build a continuous model of the
 * solution from this.
 *
 * <p>This class act as a step handler from the integrator point of
 * view. It is called iteratively during the integration process and
 * stores a copy of all steps information in a sorted collection for
 * later use. Once the integration process is over, the user can use
 * the {@link #setInterpolatedTime setInterpolatedTime} and {@link
 * #getInterpolatedState getInterpolatedState} to retrieve this
 * information at any time. It is important to wait for the
 * integration to be over before attempting to call {@link
 * #setInterpolatedTime setInterpolatedTime} because some internal
 * variables are set only once the last step has been handled.</p>
 *
 * <p>This is useful for example if the main loop of the user
 * application should remain independent from the integration process
 * or if one needs to mimic the behaviour of an analytical model
 * despite a numerical model is used (i.e. one needs the ability to
 * get the model value at any time or to navigate through the
 * data).</p>
 *
 * <p>If problem modeling is done with several separate
 * integration phases for contiguous intervals, the same
 * ContinuousOutputModel can be used as step handler for all
 * integration phases as long as they are performed in order and in
 * the same direction. As an example, one can extrapolate the
 * trajectory of a satellite with one model (i.e. one set of
 * differential equations) up to the beginning of a maneuver, use
 * another more complex model including thrusters modeling and
 * accurate attitude control during the maneuver, and revert to the
 * first model after the end of the maneuver. If the same continuous
 * output model handles the steps of all integration phases, the user
 * do not need to bother when the maneuver begins or ends, he has all
 * the data available in a transparent manner.</p>
 *
 * <p>An important feature of this class is that it implements the
 * <code>Serializable</code> interface. This means that the result of
 * an integration can be serialized and reused later (if stored into a
 * persistent medium like a filesystem or a database) or elsewhere (if
 * sent to another application). Only the result of the integration is
 * stored, there is no reference to the integrated problem by
 * itself.</p>
 *
 * <p>One should be aware that the amount of data stored in a
 * ContinuousOutputModel instance can be important if the state vector
 * is large, if the integration interval is long or if the steps are
 * small (which can result from small tolerance settings in {@link
 * org.apache.commons.math3.ode.nonstiff.AdaptiveStepsizeIntegrator adaptive
 * step size integrators}).</p>
 *
 * @see StepHandler
 * @see StepInterpolator
 * @since 1.2
 */

public class ContinuousOutputModel
  implements StepHandler, Serializable {

    /** Serializable version identifier */
    private static final long serialVersionUID = -1417964919405031606L;

    /** Initial integration time. */
    private double initialTime;

    /** Final integration time. */
    private double finalTime;

    /** Integration direction indicator. */
    private boolean forward;

    /** Current interpolator index. */
    private int index;

    /** Steps table. */
    private List<StepInterpolator> steps;

  /** Simple constructor.
   * Build an empty continuous output model.
   */
  public ContinuousOutputModel() {
    steps = new ArrayList<StepInterpolator>();
    initialTime = Double.NaN;
    finalTime   = Double.NaN;
    forward     = true;
    index       = 0;
  }

  /** Append another model at the end of the instance.
   * @param model model to add at the end of the instance
   * @exception MathIllegalArgumentException if the model to append is not
   * compatible with the instance (dimension of the state vector,
   * propagation direction, hole between the dates)
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * during step finalization
   */
  public void append(final ContinuousOutputModel model)
    throws MathIllegalArgumentException, MaxCountExceededException {

    if (model.steps.size() == 0) {
      return;
    }

    if (steps.size() == 0) {
      initialTime = model.initialTime;
      forward     = model.forward;
    } else {

      if (getInterpolatedState().length != model.getInterpolatedState().length) {
          throw new DimensionMismatchException(model.getInterpolatedState().length,
                                               getInterpolatedState().length);
      }

      if (forward ^ model.forward) {
          throw new MathIllegalArgumentException(LocalizedFormats.PROPAGATION_DIRECTION_MISMATCH);
      }

      final StepInterpolator lastInterpolator = steps.get(index);
      final double current  = lastInterpolator.getCurrentTime();
      final double previous = lastInterpolator.getPreviousTime();
      final double step = current - previous;
      final double gap = model.getInitialTime() - current;
      if (FastMath.abs(gap) > 1.0e-3 * FastMath.abs(step)) {
        throw new MathIllegalArgumentException(LocalizedFormats.HOLE_BETWEEN_MODELS_TIME_RANGES,
                                               FastMath.abs(gap));
      }

    }

    for (StepInterpolator interpolator : model.steps) {
      steps.add(interpolator.copy());
    }

    index = steps.size() - 1;
    finalTime = (steps.get(index)).getCurrentTime();

  }

  /** {@inheritDoc} */
  public void init(double t0, double[] y0, double t) {
    initialTime = Double.NaN;
    finalTime   = Double.NaN;
    forward     = true;
    index       = 0;
    steps.clear();
  }

  /** Handle the last accepted step.
   * A copy of the information provided by the last step is stored in
   * the instance for later use.
   * @param interpolator interpolator for the last accepted step.
   * @param isLast true if the step is the last one
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * during step finalization
   */
  public void handleStep(final StepInterpolator interpolator, final boolean isLast)
      throws MaxCountExceededException {

    if (steps.size() == 0) {
      initialTime = interpolator.getPreviousTime();
      forward     = interpolator.isForward();
    }

    steps.add(interpolator.copy());

    if (isLast) {
      finalTime = interpolator.getCurrentTime();
      index     = steps.size() - 1;
    }

  }

  /**
   * Get the initial integration time.
   * @return initial integration time
   */
  public double getInitialTime() {
    return initialTime;
  }

  /**
   * Get the final integration time.
   * @return final integration time
   */
  public double getFinalTime() {
    return finalTime;
  }

  /**
   * Get the time of the interpolated point.
   * If {@link #setInterpolatedTime} has not been called, it returns
   * the final integration time.
   * @return interpolation point time
   */
  public double getInterpolatedTime() {
    return steps.get(index).getInterpolatedTime();
  }

  /** Set the time of the interpolated point.
   * <p>This method should <strong>not</strong> be called before the
   * integration is over because some internal variables are set only
   * once the last step has been handled.</p>
   * <p>Setting the time outside of the integration interval is now
   * allowed, but should be used with care since the accuracy of the
   * interpolator will probably be very poor far from this interval.
   * This allowance has been added to simplify implementation of search
   * algorithms near the interval endpoints.</p>
   * <p>Note that each time this method is called, the internal arrays
   * returned in {@link #getInterpolatedState()}, {@link
   * #getInterpolatedDerivatives()} and {@link #getInterpolatedSecondaryState(int)}
   * <em>will</em> be overwritten. So if their content must be preserved
   * across several calls, user must copy them.</p>
   * @param time time of the interpolated point
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   */
  public void setInterpolatedTime(final double time) {

      // initialize the search with the complete steps table
      int iMin = 0;
      final StepInterpolator sMin = steps.get(iMin);
      double tMin = 0.5 * (sMin.getPreviousTime() + sMin.getCurrentTime());

      int iMax = steps.size() - 1;
      final StepInterpolator sMax = steps.get(iMax);
      double tMax = 0.5 * (sMax.getPreviousTime() + sMax.getCurrentTime());

      // handle points outside of the integration interval
      // or in the first and last step
      if (locatePoint(time, sMin) <= 0) {
        index = iMin;
        sMin.setInterpolatedTime(time);
        return;
      }
      if (locatePoint(time, sMax) >= 0) {
        index = iMax;
        sMax.setInterpolatedTime(time);
        return;
      }

      // reduction of the table slice size
      while (iMax - iMin > 5) {

        // use the last estimated index as the splitting index
        final StepInterpolator si = steps.get(index);
        final int location = locatePoint(time, si);
        if (location < 0) {
          iMax = index;
          tMax = 0.5 * (si.getPreviousTime() + si.getCurrentTime());
        } else if (location > 0) {
          iMin = index;
          tMin = 0.5 * (si.getPreviousTime() + si.getCurrentTime());
        } else {
          // we have found the target step, no need to continue searching
          si.setInterpolatedTime(time);
          return;
        }

        // compute a new estimate of the index in the reduced table slice
        final int iMed = (iMin + iMax) / 2;
        final StepInterpolator sMed = steps.get(iMed);
        final double tMed = 0.5 * (sMed.getPreviousTime() + sMed.getCurrentTime());

        if ((FastMath.abs(tMed - tMin) < 1e-6) || (FastMath.abs(tMax - tMed) < 1e-6)) {
          // too close to the bounds, we estimate using a simple dichotomy
          index = iMed;
        } else {
          // estimate the index using a reverse quadratic polynom
          // (reverse means we have i = P(t), thus allowing to simply
          // compute index = P(time) rather than solving a quadratic equation)
          final double d12 = tMax - tMed;
          final double d23 = tMed - tMin;
          final double d13 = tMax - tMin;
          final double dt1 = time - tMax;
          final double dt2 = time - tMed;
          final double dt3 = time - tMin;
          final double iLagrange = ((dt2 * dt3 * d23) * iMax -
                                    (dt1 * dt3 * d13) * iMed +
                                    (dt1 * dt2 * d12) * iMin) /
                                   (d12 * d23 * d13);
          index = (int) FastMath.rint(iLagrange);
        }

        // force the next size reduction to be at least one tenth
        final int low  = FastMath.max(iMin + 1, (9 * iMin + iMax) / 10);
        final int high = FastMath.min(iMax - 1, (iMin + 9 * iMax) / 10);
        if (index < low) {
          index = low;
        } else if (index > high) {
          index = high;
        }

      }

      // now the table slice is very small, we perform an iterative search
      index = iMin;
      while ((index <= iMax) && (locatePoint(time, steps.get(index)) > 0)) {
        ++index;
      }

      steps.get(index).setInterpolatedTime(time);

  }

  /**
   * Get the state vector of the interpolated point.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @return state vector at time {@link #getInterpolatedTime}
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * @see #setInterpolatedTime(double)
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   * @see #getInterpolatedSecondaryDerivatives(int)
   */
  public double[] getInterpolatedState() throws MaxCountExceededException {
    return steps.get(index).getInterpolatedState();
  }

  /**
   * Get the derivatives of the state vector of the interpolated point.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @return derivatives of the state vector at time {@link #getInterpolatedTime}
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   * @see #setInterpolatedTime(double)
   * @see #getInterpolatedState()
   * @see #getInterpolatedSecondaryState(int)
   * @see #getInterpolatedSecondaryDerivatives(int)
   * @since 3.4
   */
  public double[] getInterpolatedDerivatives() throws MaxCountExceededException {
    return steps.get(index).getInterpolatedDerivatives();
  }

  /** Get the interpolated secondary state corresponding to the secondary equations.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @param secondaryStateIndex index of the secondary set, as returned by {@link
   * org.apache.commons.math3.ode.ExpandableStatefulODE#addSecondaryEquations(
   * org.apache.commons.math3.ode.SecondaryEquations)
   * ExpandableStatefulODE.addSecondaryEquations(SecondaryEquations)}
   * @return interpolated secondary state at the current interpolation date
   * @see #setInterpolatedTime(double)
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryDerivatives(int)
   * @since 3.2
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  public double[] getInterpolatedSecondaryState(final int secondaryStateIndex)
    throws MaxCountExceededException {
    return steps.get(index).getInterpolatedSecondaryState(secondaryStateIndex);
  }

  /** Get the interpolated secondary derivatives corresponding to the secondary equations.
   * <p>The returned vector is a reference to a reused array, so
   * it should not be modified and it should be copied if it needs
   * to be preserved across several calls to the associated
   * {@link #setInterpolatedTime(double)} method.</p>
   * @param secondaryStateIndex index of the secondary set, as returned by {@link
   * org.apache.commons.math3.ode.ExpandableStatefulODE#addSecondaryEquations(
   * org.apache.commons.math3.ode.SecondaryEquations)
   * ExpandableStatefulODE.addSecondaryEquations(SecondaryEquations)}
   * @return interpolated secondary derivatives at the current interpolation date
   * @see #setInterpolatedTime(double)
   * @see #getInterpolatedState()
   * @see #getInterpolatedDerivatives()
   * @see #getInterpolatedSecondaryState(int)
   * @since 3.4
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  public double[] getInterpolatedSecondaryDerivatives(final int secondaryStateIndex)
    throws MaxCountExceededException {
    return steps.get(index).getInterpolatedSecondaryDerivatives(secondaryStateIndex);
  }

  /** Compare a step interval and a double.
   * @param time point to locate
   * @param interval step interval
   * @return -1 if the double is before the interval, 0 if it is in
   * the interval, and +1 if it is after the interval, according to
   * the interval direction
   */
  private int locatePoint(final double time, final StepInterpolator interval) {
    if (forward) {
      if (time < interval.getPreviousTime()) {
        return -1;
      } else if (time > interval.getCurrentTime()) {
        return +1;
      } else {
        return 0;
      }
    }
    if (time > interval.getPreviousTime()) {
      return -1;
    } else if (time < interval.getCurrentTime()) {
      return +1;
    } else {
      return 0;
    }
  }

}
