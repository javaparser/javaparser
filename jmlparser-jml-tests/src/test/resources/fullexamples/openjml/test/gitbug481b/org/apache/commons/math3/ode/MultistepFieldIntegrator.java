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

import org.apache.commons.math3.Field;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.linear.Array2DRowFieldMatrix;
import org.apache.commons.math3.ode.nonstiff.AdaptiveStepsizeFieldIntegrator;
import org.apache.commons.math3.ode.nonstiff.DormandPrince853FieldIntegrator;
import org.apache.commons.math3.ode.sampling.FieldStepHandler;
import org.apache.commons.math3.ode.sampling.FieldStepInterpolator;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;

/**
 * This class is the base class for multistep integrators for Ordinary
 * Differential Equations.
 * <p>We define scaled derivatives s<sub>i</sub>(n) at step n as:
 * <pre>
 * s<sub>1</sub>(n) = h y'<sub>n</sub> for first derivative
 * s<sub>2</sub>(n) = h<sup>2</sup>/2 y''<sub>n</sub> for second derivative
 * s<sub>3</sub>(n) = h<sup>3</sup>/6 y'''<sub>n</sub> for third derivative
 * ...
 * s<sub>k</sub>(n) = h<sup>k</sup>/k! y<sup>(k)</sup><sub>n</sub> for k<sup>th</sup> derivative
 * </pre></p>
 * <p>Rather than storing several previous steps separately, this implementation uses
 * the Nordsieck vector with higher degrees scaled derivatives all taken at the same
 * step (y<sub>n</sub>, s<sub>1</sub>(n) and r<sub>n</sub>) where r<sub>n</sub> is defined as:
 * <pre>
 * r<sub>n</sub> = [ s<sub>2</sub>(n), s<sub>3</sub>(n) ... s<sub>k</sub>(n) ]<sup>T</sup>
 * </pre>
 * (we omit the k index in the notation for clarity)</p>
 * <p>
 * Multistep integrators with Nordsieck representation are highly sensitive to
 * large step changes because when the step is multiplied by factor a, the
 * k<sup>th</sup> component of the Nordsieck vector is multiplied by a<sup>k</sup>
 * and the last components are the least accurate ones. The default max growth
 * factor is therefore set to a quite low value: 2<sup>1/order</sup>.
 * </p>
 *
 * @see org.apache.commons.math3.ode.nonstiff.AdamsBashforthFieldIntegrator
 * @see org.apache.commons.math3.ode.nonstiff.AdamsMoultonFieldIntegrator
 * @param <T> the type of the field elements
 * @since 3.6
 */
public abstract class MultistepFieldIntegrator<T extends RealFieldElement<T>>
    extends AdaptiveStepsizeFieldIntegrator<T> {

    /** First scaled derivative (h y'). */
    protected T[] scaled;

    /** Nordsieck matrix of the higher scaled derivatives.
     * <p>(h<sup>2</sup>/2 y'', h<sup>3</sup>/6 y''' ..., h<sup>k</sup>/k! y<sup>(k)</sup>)</p>
     */
    protected Array2DRowFieldMatrix<T> nordsieck;

    /** Starter integrator. */
    private FirstOrderFieldIntegrator<T> starter;

    /** Number of steps of the multistep method (excluding the one being computed). */
    private final int nSteps;

    /** Stepsize control exponent. */
    private double exp;

    /** Safety factor for stepsize control. */
    private double safety;

    /** Minimal reduction factor for stepsize control. */
    private double minReduction;

    /** Maximal growth factor for stepsize control. */
    private double maxGrowth;

    /**
     * Build a multistep integrator with the given stepsize bounds.
     * <p>The default starter integrator is set to the {@link
     * DormandPrince853FieldIntegrator Dormand-Prince 8(5,3)} integrator with
     * some defaults settings.</p>
     * <p>
     * The default max growth factor is set to a quite low value: 2<sup>1/order</sup>.
     * </p>
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param nSteps number of steps of the multistep method
     * (excluding the one being computed)
     * @param order order of the method
     * @param minStep minimal step (must be positive even for backward
     * integration), the last step can be smaller than this
     * @param maxStep maximal step (must be positive even for backward
     * integration)
     * @param scalAbsoluteTolerance allowed absolute error
     * @param scalRelativeTolerance allowed relative error
     * @exception NumberIsTooSmallException if number of steps is smaller than 2
     */
    protected MultistepFieldIntegrator(final Field<T> field, final String name,
                                       final int nSteps, final int order,
                                       final double minStep, final double maxStep,
                                       final double scalAbsoluteTolerance,
                                       final double scalRelativeTolerance)
        throws NumberIsTooSmallException {

        super(field, name, minStep, maxStep, scalAbsoluteTolerance, scalRelativeTolerance);

        if (nSteps < 2) {
            throw new NumberIsTooSmallException(
                  LocalizedFormats.INTEGRATION_METHOD_NEEDS_AT_LEAST_TWO_PREVIOUS_POINTS,
                  nSteps, 2, true);
        }

        starter = new DormandPrince853FieldIntegrator<T>(field, minStep, maxStep,
                                                         scalAbsoluteTolerance,
                                                         scalRelativeTolerance);
        this.nSteps = nSteps;

        exp = -1.0 / order;

        // set the default values of the algorithm control parameters
        setSafety(0.9);
        setMinReduction(0.2);
        setMaxGrowth(FastMath.pow(2.0, -exp));

    }

    /**
     * Build a multistep integrator with the given stepsize bounds.
     * <p>The default starter integrator is set to the {@link
     * DormandPrince853FieldIntegrator Dormand-Prince 8(5,3)} integrator with
     * some defaults settings.</p>
     * <p>
     * The default max growth factor is set to a quite low value: 2<sup>1/order</sup>.
     * </p>
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param nSteps number of steps of the multistep method
     * (excluding the one being computed)
     * @param order order of the method
     * @param minStep minimal step (must be positive even for backward
     * integration), the last step can be smaller than this
     * @param maxStep maximal step (must be positive even for backward
     * integration)
     * @param vecAbsoluteTolerance allowed absolute error
     * @param vecRelativeTolerance allowed relative error
     */
    protected MultistepFieldIntegrator(final Field<T> field, final String name, final int nSteps,
                                       final int order,
                                       final double minStep, final double maxStep,
                                       final double[] vecAbsoluteTolerance,
                                       final double[] vecRelativeTolerance) {
        super(field, name, minStep, maxStep, vecAbsoluteTolerance, vecRelativeTolerance);
        starter = new DormandPrince853FieldIntegrator<T>(field, minStep, maxStep,
                                                         vecAbsoluteTolerance,
                                                         vecRelativeTolerance);
        this.nSteps = nSteps;

        exp = -1.0 / order;

        // set the default values of the algorithm control parameters
        setSafety(0.9);
        setMinReduction(0.2);
        setMaxGrowth(FastMath.pow(2.0, -exp));

    }

    /**
     * Get the starter integrator.
     * @return starter integrator
     */
    public FirstOrderFieldIntegrator<T> getStarterIntegrator() {
        return starter;
    }

    /**
     * Set the starter integrator.
     * <p>The various step and event handlers for this starter integrator
     * will be managed automatically by the multi-step integrator. Any
     * user configuration for these elements will be cleared before use.</p>
     * @param starterIntegrator starter integrator
     */
    public void setStarterIntegrator(FirstOrderFieldIntegrator<T> starterIntegrator) {
        this.starter = starterIntegrator;
    }

    /** Start the integration.
     * <p>This method computes one step using the underlying starter integrator,
     * and initializes the Nordsieck vector at step start. The starter integrator
     * purpose is only to establish initial conditions, it does not really change
     * time by itself. The top level multistep integrator remains in charge of
     * handling time propagation and events handling as it will starts its own
     * computation right from the beginning. In a sense, the starter integrator
     * can be seen as a dummy one and so it will never trigger any user event nor
     * call any user step handler.</p>
     * @param equations complete set of differential equations to integrate
     * @param initialState initial state (time, primary and secondary state vectors)
     * @param t target time for the integration
     * (can be set to a value smaller than <code>t0</code> for backward integration)
     * @exception DimensionMismatchException if arrays dimension do not match equations settings
     * @exception NumberIsTooSmallException if integration step is too small
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception NoBracketingException if the location of an event cannot be bracketed
     */
    protected void start(final FieldExpandableODE<T> equations, final FieldODEState<T> initialState, final T t)
        throws DimensionMismatchException, NumberIsTooSmallException,
               MaxCountExceededException, NoBracketingException {

        // make sure NO user event nor user step handler is triggered,
        // this is the task of the top level integrator, not the task
        // of the starter integrator
        starter.clearEventHandlers();
        starter.clearStepHandlers();

        // set up one specific step handler to extract initial Nordsieck vector
        starter.addStepHandler(new FieldNordsieckInitializer(equations.getMapper(), (nSteps + 3) / 2));

        // start integration, expecting a InitializationCompletedMarkerException
        try {

            starter.integrate(equations, initialState, t);

            // we should not reach this step
            throw new MathIllegalStateException(LocalizedFormats.MULTISTEP_STARTER_STOPPED_EARLY);

        } catch (InitializationCompletedMarkerException icme) { // NOPMD
            // this is the expected nominal interruption of the start integrator

            // count the evaluations used by the starter
            getEvaluationsCounter().increment(starter.getEvaluations());

        }

        // remove the specific step handler
        starter.clearStepHandlers();

    }

    /** Initialize the high order scaled derivatives at step start.
     * @param h step size to use for scaling
     * @param t first steps times
     * @param y first steps states
     * @param yDot first steps derivatives
     * @return Nordieck vector at first step (h<sup>2</sup>/2 y''<sub>n</sub>,
     * h<sup>3</sup>/6 y'''<sub>n</sub> ... h<sup>k</sup>/k! y<sup>(k)</sup><sub>n</sub>)
     */
    protected abstract Array2DRowFieldMatrix<T> initializeHighOrderDerivatives(final T h, final T[] t,
                                                                               final T[][] y,
                                                                               final T[][] yDot);

    /** Get the minimal reduction factor for stepsize control.
     * @return minimal reduction factor
     */
    public double getMinReduction() {
        return minReduction;
    }

    /** Set the minimal reduction factor for stepsize control.
     * @param minReduction minimal reduction factor
     */
    public void setMinReduction(final double minReduction) {
        this.minReduction = minReduction;
    }

    /** Get the maximal growth factor for stepsize control.
     * @return maximal growth factor
     */
    public double getMaxGrowth() {
        return maxGrowth;
    }

    /** Set the maximal growth factor for stepsize control.
     * @param maxGrowth maximal growth factor
     */
    public void setMaxGrowth(final double maxGrowth) {
        this.maxGrowth = maxGrowth;
    }

    /** Get the safety factor for stepsize control.
     * @return safety factor
     */
    public double getSafety() {
      return safety;
    }

    /** Set the safety factor for stepsize control.
     * @param safety safety factor
     */
    public void setSafety(final double safety) {
      this.safety = safety;
    }

    /** Get the number of steps of the multistep method (excluding the one being computed).
     * @return number of steps of the multistep method (excluding the one being computed)
     */
    public int getNSteps() {
      return nSteps;
    }

    /** Rescale the instance.
     * <p>Since the scaled and Nordsieck arrays are shared with the caller,
     * this method has the side effect of rescaling this arrays in the caller too.</p>
     * @param newStepSize new step size to use in the scaled and Nordsieck arrays
     */
    protected void rescale(final T newStepSize) {

        final T ratio = newStepSize.divide(getStepSize());
        for (int i = 0; i < scaled.length; ++i) {
            scaled[i] = scaled[i].multiply(ratio);
        }

        final T[][] nData = nordsieck.getDataRef();
        T power = ratio;
        for (int i = 0; i < nData.length; ++i) {
            power = power.multiply(ratio);
            final T[] nDataI = nData[i];
            for (int j = 0; j < nDataI.length; ++j) {
                nDataI[j] = nDataI[j].multiply(power);
            }
        }

        setStepSize(newStepSize);

    }


    /** Compute step grow/shrink factor according to normalized error.
     * @param error normalized error of the current step
     * @return grow/shrink factor for next step
     */
    protected T computeStepGrowShrinkFactor(final T error) {
        return MathUtils.min(error.getField().getZero().add(maxGrowth),
                             MathUtils.max(error.getField().getZero().add(minReduction),
                                           error.pow(exp).multiply(safety)));
    }

    /** Specialized step handler storing the first step.
     */
    private class FieldNordsieckInitializer implements FieldStepHandler<T> {

        /** Equation mapper. */
        private final FieldEquationsMapper<T> mapper;

        /** Steps counter. */
        private int count;

        /** Saved start. */
        private FieldODEStateAndDerivative<T> savedStart;

        /** First steps times. */
        private final T[] t;

        /** First steps states. */
        private final T[][] y;

        /** First steps derivatives. */
        private final T[][] yDot;

        /** Simple constructor.
         * @param mapper equation mapper
         * @param nbStartPoints number of start points (including the initial point)
         */
        FieldNordsieckInitializer(final FieldEquationsMapper<T> mapper, final int nbStartPoints) {
            this.mapper = mapper;
            this.count  = 0;
            this.t      = MathArrays.buildArray(getField(), nbStartPoints);
            this.y      = MathArrays.buildArray(getField(), nbStartPoints, -1);
            this.yDot   = MathArrays.buildArray(getField(), nbStartPoints, -1);
        }

        /** {@inheritDoc} */
        public void handleStep(FieldStepInterpolator<T> interpolator, boolean isLast)
            throws MaxCountExceededException {


            if (count == 0) {
                // first step, we need to store also the point at the beginning of the step
                final FieldODEStateAndDerivative<T> prev = interpolator.getPreviousState();
                savedStart  = prev;
                t[count]    = prev.getTime();
                y[count]    = mapper.mapState(prev);
                yDot[count] = mapper.mapDerivative(prev);
            }

            // store the point at the end of the step
            ++count;
            final FieldODEStateAndDerivative<T> curr = interpolator.getCurrentState();
            t[count]    = curr.getTime();
            y[count]    = mapper.mapState(curr);
            yDot[count] = mapper.mapDerivative(curr);

            if (count == t.length - 1) {

                // this was the last point we needed, we can compute the derivatives
                setStepSize(t[t.length - 1].subtract(t[0]).divide(t.length - 1));

                // first scaled derivative
                scaled = MathArrays.buildArray(getField(), yDot[0].length);
                for (int j = 0; j < scaled.length; ++j) {
                    scaled[j] = yDot[0][j].multiply(getStepSize());
                }

                // higher order derivatives
                nordsieck = initializeHighOrderDerivatives(getStepSize(), t, y, yDot);

                // stop the integrator now that all needed steps have been handled
                setStepStart(savedStart);
                throw new InitializationCompletedMarkerException();

            }

        }

        /** {@inheritDoc} */
        public void init(final FieldODEStateAndDerivative<T> initialState, T finalTime) {
            // nothing to do
        }

    }

    /** Marker exception used ONLY to stop the starter integrator after first step. */
    private static class InitializationCompletedMarkerException
        extends RuntimeException {

        /** Serializable version identifier. */
        private static final long serialVersionUID = -1914085471038046418L;

        /** Simple constructor. */
        InitializationCompletedMarkerException() {
            super((Throwable) null);
        }

    }

}
