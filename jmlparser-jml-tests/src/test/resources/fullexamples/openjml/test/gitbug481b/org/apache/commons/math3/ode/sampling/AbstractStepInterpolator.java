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

package org.apache.commons.math3.ode.sampling;

import java.io.IOException;
import java.io.ObjectInput;
import java.io.ObjectOutput;

import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.ode.EquationsMapper;

/** This abstract class represents an interpolator over the last step
 * during an ODE integration.
 *
 * <p>The various ODE integrators provide objects extending this class
 * to the step handlers. The handlers can use these objects to
 * retrieve the state vector at intermediate times between the
 * previous and the current grid points (dense output).</p>
 *
 * @see org.apache.commons.math3.ode.FirstOrderIntegrator
 * @see org.apache.commons.math3.ode.SecondOrderIntegrator
 * @see StepHandler
 *
 * @since 1.2
 *
 */

public abstract class AbstractStepInterpolator
  implements StepInterpolator {

  /** current time step */
  protected double h;

  /** current state */
  protected double[] currentState;

  /** interpolated time */
  protected double interpolatedTime;

  /** interpolated state */
  protected double[] interpolatedState;

  /** interpolated derivatives */
  protected double[] interpolatedDerivatives;

  /** interpolated primary state */
  protected double[] interpolatedPrimaryState;

  /** interpolated primary derivatives */
  protected double[] interpolatedPrimaryDerivatives;

  /** interpolated secondary state */
  protected double[][] interpolatedSecondaryState;

  /** interpolated secondary derivatives */
  protected double[][] interpolatedSecondaryDerivatives;

  /** global previous time */
  private double globalPreviousTime;

  /** global current time */
  private double globalCurrentTime;

  /** soft previous time */
  private double softPreviousTime;

  /** soft current time */
  private double softCurrentTime;

  /** indicate if the step has been finalized or not. */
  private boolean finalized;

  /** integration direction. */
  private boolean forward;

  /** indicator for dirty state. */
  private boolean dirtyState;

  /** Equations mapper for the primary equations set. */
  private EquationsMapper primaryMapper;

  /** Equations mappers for the secondary equations sets. */
  private EquationsMapper[] secondaryMappers;

  /** Simple constructor.
   * This constructor builds an instance that is not usable yet, the
   * {@link #reinitialize} method should be called before using the
   * instance in order to initialize the internal arrays. This
   * constructor is used only in order to delay the initialization in
   * some cases. As an example, the {@link
   * org.apache.commons.math3.ode.nonstiff.EmbeddedRungeKuttaIntegrator}
   * class uses the prototyping design pattern to create the step
   * interpolators by cloning an uninitialized model and latter
   * initializing the copy.
   */
  protected AbstractStepInterpolator() {
    globalPreviousTime = Double.NaN;
    globalCurrentTime  = Double.NaN;
    softPreviousTime   = Double.NaN;
    softCurrentTime    = Double.NaN;
    h                  = Double.NaN;
    interpolatedTime   = Double.NaN;
    currentState       = null;
    finalized          = false;
    this.forward       = true;
    this.dirtyState    = true;
    primaryMapper      = null;
    secondaryMappers   = null;
    allocateInterpolatedArrays(-1);
  }

  /** Simple constructor.
   * @param y reference to the integrator array holding the state at
   * the end of the step
   * @param forward integration direction indicator
   * @param primaryMapper equations mapper for the primary equations set
   * @param secondaryMappers equations mappers for the secondary equations sets
   */
  protected AbstractStepInterpolator(final double[] y, final boolean forward,
                                     final EquationsMapper primaryMapper,
                                     final EquationsMapper[] secondaryMappers) {

    globalPreviousTime    = Double.NaN;
    globalCurrentTime     = Double.NaN;
    softPreviousTime      = Double.NaN;
    softCurrentTime       = Double.NaN;
    h                     = Double.NaN;
    interpolatedTime      = Double.NaN;
    currentState          = y;
    finalized             = false;
    this.forward          = forward;
    this.dirtyState       = true;
    this.primaryMapper    = primaryMapper;
    this.secondaryMappers = (secondaryMappers == null) ? null : secondaryMappers.clone();
    allocateInterpolatedArrays(y.length);

  }

  /** Copy constructor.

   * <p>The copied interpolator should have been finalized before the
   * copy, otherwise the copy will not be able to perform correctly
   * any derivative computation and will throw a {@link
   * NullPointerException} later. Since we don't want this constructor
   * to throw the exceptions finalization may involve and since we
   * don't want this method to modify the state of the copied
   * interpolator, finalization is <strong>not</strong> done
   * automatically, it remains under user control.</p>

   * <p>The copy is a deep copy: its arrays are separated from the
   * original arrays of the instance.</p>

   * @param interpolator interpolator to copy from.

   */
  protected AbstractStepInterpolator(final AbstractStepInterpolator interpolator) {

    globalPreviousTime = interpolator.globalPreviousTime;
    globalCurrentTime  = interpolator.globalCurrentTime;
    softPreviousTime   = interpolator.softPreviousTime;
    softCurrentTime    = interpolator.softCurrentTime;
    h                  = interpolator.h;
    interpolatedTime   = interpolator.interpolatedTime;

    if (interpolator.currentState == null) {
        currentState     = null;
        primaryMapper    = null;
        secondaryMappers = null;
        allocateInterpolatedArrays(-1);
    } else {
      currentState                     = interpolator.currentState.clone();
      interpolatedState                = interpolator.interpolatedState.clone();
      interpolatedDerivatives          = interpolator.interpolatedDerivatives.clone();
      interpolatedPrimaryState         = interpolator.interpolatedPrimaryState.clone();
      interpolatedPrimaryDerivatives   = interpolator.interpolatedPrimaryDerivatives.clone();
      interpolatedSecondaryState       = new double[interpolator.interpolatedSecondaryState.length][];
      interpolatedSecondaryDerivatives = new double[interpolator.interpolatedSecondaryDerivatives.length][];
      for (int i = 0; i < interpolatedSecondaryState.length; ++i) {
          interpolatedSecondaryState[i]       = interpolator.interpolatedSecondaryState[i].clone();
          interpolatedSecondaryDerivatives[i] = interpolator.interpolatedSecondaryDerivatives[i].clone();
      }
    }

    finalized        = interpolator.finalized;
    forward          = interpolator.forward;
    dirtyState       = interpolator.dirtyState;
    primaryMapper    = interpolator.primaryMapper;
    secondaryMappers = (interpolator.secondaryMappers == null) ?
                       null : interpolator.secondaryMappers.clone();

  }

  /** Allocate the various interpolated states arrays.
   * @param dimension total dimension (negative if arrays should be set to null)
   */
  private void allocateInterpolatedArrays(final int dimension) {
      if (dimension < 0) {
          interpolatedState                = null;
          interpolatedDerivatives          = null;
          interpolatedPrimaryState         = null;
          interpolatedPrimaryDerivatives   = null;
          interpolatedSecondaryState       = null;
          interpolatedSecondaryDerivatives = null;
      } else {
          interpolatedState                = new double[dimension];
          interpolatedDerivatives          = new double[dimension];
          interpolatedPrimaryState         = new double[primaryMapper.getDimension()];
          interpolatedPrimaryDerivatives   = new double[primaryMapper.getDimension()];
          if (secondaryMappers == null) {
              interpolatedSecondaryState       = null;
              interpolatedSecondaryDerivatives = null;
          } else {
              interpolatedSecondaryState       = new double[secondaryMappers.length][];
              interpolatedSecondaryDerivatives = new double[secondaryMappers.length][];
              for (int i = 0; i < secondaryMappers.length; ++i) {
                  interpolatedSecondaryState[i]       = new double[secondaryMappers[i].getDimension()];
                  interpolatedSecondaryDerivatives[i] = new double[secondaryMappers[i].getDimension()];
              }
          }
      }
  }

  /** Reinitialize the instance
   * @param y reference to the integrator array holding the state at the end of the step
   * @param isForward integration direction indicator
   * @param primary equations mapper for the primary equations set
   * @param secondary equations mappers for the secondary equations sets
   */
  protected void reinitialize(final double[] y, final boolean isForward,
                              final EquationsMapper primary,
                              final EquationsMapper[] secondary) {

    globalPreviousTime    = Double.NaN;
    globalCurrentTime     = Double.NaN;
    softPreviousTime      = Double.NaN;
    softCurrentTime       = Double.NaN;
    h                     = Double.NaN;
    interpolatedTime      = Double.NaN;
    currentState          = y;
    finalized             = false;
    this.forward          = isForward;
    this.dirtyState       = true;
    this.primaryMapper    = primary;
    this.secondaryMappers = secondary.clone();
    allocateInterpolatedArrays(y.length);

  }

  /** {@inheritDoc} */
   public StepInterpolator copy() throws MaxCountExceededException {

     // finalize the step before performing copy
     finalizeStep();

     // create the new independent instance
     return doCopy();

   }

   /** Really copy the finalized instance.
    * <p>This method is called by {@link #copy()} after the
    * step has been finalized. It must perform a deep copy
    * to have an new instance completely independent for the
    * original instance.
    * @return a copy of the finalized instance
    */
   protected abstract StepInterpolator doCopy();

  /** Shift one step forward.
   * Copy the current time into the previous time, hence preparing the
   * interpolator for future calls to {@link #storeTime storeTime}
   */
  public void shift() {
    globalPreviousTime = globalCurrentTime;
    softPreviousTime   = globalPreviousTime;
    softCurrentTime    = globalCurrentTime;
  }

  /** Store the current step time.
   * @param t current time
   */
  public void storeTime(final double t) {

    globalCurrentTime = t;
    softCurrentTime   = globalCurrentTime;
    h                 = globalCurrentTime - globalPreviousTime;
    setInterpolatedTime(t);

    // the step is not finalized anymore
    finalized  = false;

  }

  /** Restrict step range to a limited part of the global step.
   * <p>
   * This method can be used to restrict a step and make it appear
   * as if the original step was smaller. Calling this method
   * <em>only</em> changes the value returned by {@link #getPreviousTime()},
   * it does not change any other property
   * </p>
   * @param softPreviousTime start of the restricted step
   * @since 2.2
   */
  public void setSoftPreviousTime(final double softPreviousTime) {
      this.softPreviousTime = softPreviousTime;
  }

  /** Restrict step range to a limited part of the global step.
   * <p>
   * This method can be used to restrict a step and make it appear
   * as if the original step was smaller. Calling this method
   * <em>only</em> changes the value returned by {@link #getCurrentTime()},
   * it does not change any other property
   * </p>
   * @param softCurrentTime end of the restricted step
   * @since 2.2
   */
  public void setSoftCurrentTime(final double softCurrentTime) {
      this.softCurrentTime  = softCurrentTime;
  }

  /**
   * Get the previous global grid point time.
   * @return previous global grid point time
   */
  public double getGlobalPreviousTime() {
    return globalPreviousTime;
  }

  /**
   * Get the current global grid point time.
   * @return current global grid point time
   */
  public double getGlobalCurrentTime() {
    return globalCurrentTime;
  }

  /**
   * Get the previous soft grid point time.
   * @return previous soft grid point time
   * @see #setSoftPreviousTime(double)
   */
  public double getPreviousTime() {
    return softPreviousTime;
  }

  /**
   * Get the current soft grid point time.
   * @return current soft grid point time
   * @see #setSoftCurrentTime(double)
   */
  public double getCurrentTime() {
    return softCurrentTime;
  }

  /** {@inheritDoc} */
  public double getInterpolatedTime() {
    return interpolatedTime;
  }

  /** {@inheritDoc} */
  public void setInterpolatedTime(final double time) {
      interpolatedTime = time;
      dirtyState       = true;
  }

  /** {@inheritDoc} */
  public boolean isForward() {
    return forward;
  }

  /** Compute the state and derivatives at the interpolated time.
   * This is the main processing method that should be implemented by
   * the derived classes to perform the interpolation.
   * @param theta normalized interpolation abscissa within the step
   * (theta is zero at the previous time step and one at the current time step)
   * @param oneMinusThetaH time gap between the interpolated time and
   * the current time
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  protected abstract void computeInterpolatedStateAndDerivatives(double theta,
                                                                 double oneMinusThetaH)
      throws MaxCountExceededException;

  /** Lazy evaluation of complete interpolated state.
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  private void evaluateCompleteInterpolatedState()
      throws MaxCountExceededException {
      // lazy evaluation of the state
      if (dirtyState) {
          final double oneMinusThetaH = globalCurrentTime - interpolatedTime;
          final double theta = (h == 0) ? 0 : (h - oneMinusThetaH) / h;
          computeInterpolatedStateAndDerivatives(theta, oneMinusThetaH);
          dirtyState = false;
      }
  }

  /** {@inheritDoc} */
  public double[] getInterpolatedState() throws MaxCountExceededException {
      evaluateCompleteInterpolatedState();
      primaryMapper.extractEquationData(interpolatedState,
                                        interpolatedPrimaryState);
      return interpolatedPrimaryState;
  }

  /** {@inheritDoc} */
  public double[] getInterpolatedDerivatives() throws MaxCountExceededException {
      evaluateCompleteInterpolatedState();
      primaryMapper.extractEquationData(interpolatedDerivatives,
                                        interpolatedPrimaryDerivatives);
      return interpolatedPrimaryDerivatives;
  }

  /** {@inheritDoc} */
  public double[] getInterpolatedSecondaryState(final int index) throws MaxCountExceededException {
      evaluateCompleteInterpolatedState();
      secondaryMappers[index].extractEquationData(interpolatedState,
                                                  interpolatedSecondaryState[index]);
      return interpolatedSecondaryState[index];
  }

  /** {@inheritDoc} */
  public double[] getInterpolatedSecondaryDerivatives(final int index) throws MaxCountExceededException {
      evaluateCompleteInterpolatedState();
      secondaryMappers[index].extractEquationData(interpolatedDerivatives,
                                                  interpolatedSecondaryDerivatives[index]);
      return interpolatedSecondaryDerivatives[index];
  }

  /**
   * Finalize the step.

   * <p>Some embedded Runge-Kutta integrators need fewer functions
   * evaluations than their counterpart step interpolators. These
   * interpolators should perform the last evaluations they need by
   * themselves only if they need them. This method triggers these
   * extra evaluations. It can be called directly by the user step
   * handler and it is called automatically if {@link
   * #setInterpolatedTime} is called.</p>

   * <p>Once this method has been called, <strong>no</strong> other
   * evaluation will be performed on this step. If there is a need to
   * have some side effects between the step handler and the
   * differential equations (for example update some data in the
   * equations once the step has been done), it is advised to call
   * this method explicitly from the step handler before these side
   * effects are set up. If the step handler induces no side effect,
   * then this method can safely be ignored, it will be called
   * transparently as needed.</p>

   * <p><strong>Warning</strong>: since the step interpolator provided
   * to the step handler as a parameter of the {@link
   * StepHandler#handleStep handleStep} is valid only for the duration
   * of the {@link StepHandler#handleStep handleStep} call, one cannot
   * simply store a reference and reuse it later. One should first
   * finalize the instance, then copy this finalized instance into a
   * new object that can be kept.</p>

   * <p>This method calls the protected <code>doFinalize</code> method
   * if it has never been called during this step and set a flag
   * indicating that it has been called once. It is the <code>
   * doFinalize</code> method which should perform the evaluations.
   * This wrapping prevents from calling <code>doFinalize</code> several
   * times and hence evaluating the differential equations too often.
   * Therefore, subclasses are not allowed not reimplement it, they
   * should rather reimplement <code>doFinalize</code>.</p>

   * @exception MaxCountExceededException if the number of functions evaluations is exceeded

   */
  public final void finalizeStep() throws MaxCountExceededException {
    if (! finalized) {
      doFinalize();
      finalized = true;
    }
  }

  /**
   * Really finalize the step.
   * The default implementation of this method does nothing.
   * @exception MaxCountExceededException if the number of functions evaluations is exceeded
   */
  protected void doFinalize() throws MaxCountExceededException {
  }

  /** {@inheritDoc} */
  public abstract void writeExternal(ObjectOutput out)
    throws IOException;

  /** {@inheritDoc} */
  public abstract void readExternal(ObjectInput in)
    throws IOException, ClassNotFoundException;

  /** Save the base state of the instance.
   * This method performs step finalization if it has not been done
   * before.
   * @param out stream where to save the state
   * @exception IOException in case of write error
   */
  protected void writeBaseExternal(final ObjectOutput out)
    throws IOException {

    if (currentState == null) {
        out.writeInt(-1);
    } else {
        out.writeInt(currentState.length);
    }
    out.writeDouble(globalPreviousTime);
    out.writeDouble(globalCurrentTime);
    out.writeDouble(softPreviousTime);
    out.writeDouble(softCurrentTime);
    out.writeDouble(h);
    out.writeBoolean(forward);
    out.writeObject(primaryMapper);
    out.write(secondaryMappers.length);
    for (final EquationsMapper  mapper : secondaryMappers) {
        out.writeObject(mapper);
    }

    if (currentState != null) {
        for (int i = 0; i < currentState.length; ++i) {
            out.writeDouble(currentState[i]);
        }
    }

    out.writeDouble(interpolatedTime);

    // we do not store the interpolated state,
    // it will be recomputed as needed after reading

    try {
        // finalize the step (and don't bother saving the now true flag)
        finalizeStep();
    } catch (MaxCountExceededException mcee) {
        final IOException ioe = new IOException(mcee.getLocalizedMessage());
        ioe.initCause(mcee);
        throw ioe;
    }

  }

  /** Read the base state of the instance.
   * This method does <strong>neither</strong> set the interpolated
   * time nor state. It is up to the derived class to reset it
   * properly calling the {@link #setInterpolatedTime} method later,
   * once all rest of the object state has been set up properly.
   * @param in stream where to read the state from
   * @return interpolated time to be set later by the caller
   * @exception IOException in case of read error
   * @exception ClassNotFoundException if an equation mapper class
   * cannot be found
   */
  protected double readBaseExternal(final ObjectInput in)
    throws IOException, ClassNotFoundException {

    final int dimension = in.readInt();
    globalPreviousTime  = in.readDouble();
    globalCurrentTime   = in.readDouble();
    softPreviousTime    = in.readDouble();
    softCurrentTime     = in.readDouble();
    h                   = in.readDouble();
    forward             = in.readBoolean();
    primaryMapper       = (EquationsMapper) in.readObject();
    secondaryMappers    = new EquationsMapper[in.read()];
    for (int i = 0; i < secondaryMappers.length; ++i) {
        secondaryMappers[i] = (EquationsMapper) in.readObject();
    }
    dirtyState          = true;

    if (dimension < 0) {
        currentState = null;
    } else {
        currentState  = new double[dimension];
        for (int i = 0; i < currentState.length; ++i) {
            currentState[i] = in.readDouble();
        }
    }

    // we do NOT handle the interpolated time and state here
    interpolatedTime = Double.NaN;
    allocateInterpolatedArrays(dimension);

    finalized = true;

    return in.readDouble();

  }

}
