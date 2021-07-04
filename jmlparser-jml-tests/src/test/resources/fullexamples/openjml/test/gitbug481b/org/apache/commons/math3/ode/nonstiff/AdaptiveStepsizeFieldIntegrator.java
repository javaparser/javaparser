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

package org.apache.commons.math3.ode.nonstiff;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.ode.AbstractFieldIntegrator;
import org.apache.commons.math3.ode.FieldEquationsMapper;
import org.apache.commons.math3.ode.FieldODEState;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;

/**
 * This abstract class holds the common part of all adaptive
 * stepsize integrators for Ordinary Differential Equations.
 *
 * <p>These algorithms perform integration with stepsize control, which
 * means the user does not specify the integration step but rather a
 * tolerance on error. The error threshold is computed as
 * <pre>
 * threshold_i = absTol_i + relTol_i * max (abs (ym), abs (ym+1))
 * </pre>
 * where absTol_i is the absolute tolerance for component i of the
 * state vector and relTol_i is the relative tolerance for the same
 * component. The user can also use only two scalar values absTol and
 * relTol which will be used for all components.
 * </p>
 * <p>
 * Note that <em>only</em> the {@link FieldODEState#getState() main part}
 * of the state vector is used for stepsize control. The {@link
 * FieldODEState#getSecondaryState(int) secondary parts} of the state
 * vector are explicitly ignored for stepsize control.
 * </p>
 *
 * <p>If the estimated error for ym+1 is such that
 * <pre>
 * sqrt((sum (errEst_i / threshold_i)^2 ) / n) < 1
 * </pre>
 *
 * (where n is the main set dimension) then the step is accepted,
 * otherwise the step is rejected and a new attempt is made with a new
 * stepsize.</p>
 *
 * @param <T> the type of the field elements
 * @since 3.6
 *
 */

public abstract class AdaptiveStepsizeFieldIntegrator<T extends RealFieldElement<T>>
    extends AbstractFieldIntegrator<T> {

    /** Allowed absolute scalar error. */
    protected double scalAbsoluteTolerance;

    /** Allowed relative scalar error. */
    protected double scalRelativeTolerance;

    /** Allowed absolute vectorial error. */
    protected double[] vecAbsoluteTolerance;

    /** Allowed relative vectorial error. */
    protected double[] vecRelativeTolerance;

    /** Main set dimension. */
    protected int mainSetDimension;

    /** User supplied initial step. */
    private T initialStep;

    /** Minimal step. */
    private T minStep;

    /** Maximal step. */
    private T maxStep;

    /** Build an integrator with the given stepsize bounds.
     * The default step handler does nothing.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param minStep minimal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param maxStep maximal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param scalAbsoluteTolerance allowed absolute error
     * @param scalRelativeTolerance allowed relative error
     */
    public AdaptiveStepsizeFieldIntegrator(final Field<T> field, final String name,
                                           final double minStep, final double maxStep,
                                           final double scalAbsoluteTolerance,
                                           final double scalRelativeTolerance) {

        super(field, name);
        setStepSizeControl(minStep, maxStep, scalAbsoluteTolerance, scalRelativeTolerance);
        resetInternalState();

    }

    /** Build an integrator with the given stepsize bounds.
     * The default step handler does nothing.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param minStep minimal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param maxStep maximal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param vecAbsoluteTolerance allowed absolute error
     * @param vecRelativeTolerance allowed relative error
     */
    public AdaptiveStepsizeFieldIntegrator(final Field<T> field, final String name,
                                           final double minStep, final double maxStep,
                                           final double[] vecAbsoluteTolerance,
                                           final double[] vecRelativeTolerance) {

        super(field, name);
        setStepSizeControl(minStep, maxStep, vecAbsoluteTolerance, vecRelativeTolerance);
        resetInternalState();

    }

    /** Set the adaptive step size control parameters.
     * <p>
     * A side effect of this method is to also reset the initial
     * step so it will be automatically computed by the integrator
     * if {@link #setInitialStepSize(RealFieldElement) setInitialStepSize}
     * is not called by the user.
     * </p>
     * @param minimalStep minimal step (must be positive even for backward
     * integration), the last step can be smaller than this
     * @param maximalStep maximal step (must be positive even for backward
     * integration)
     * @param absoluteTolerance allowed absolute error
     * @param relativeTolerance allowed relative error
     */
    public void setStepSizeControl(final double minimalStep, final double maximalStep,
                                   final double absoluteTolerance,
                                   final double relativeTolerance) {

        minStep     = getField().getZero().add(FastMath.abs(minimalStep));
        maxStep     = getField().getZero().add(FastMath.abs(maximalStep));
        initialStep = getField().getOne().negate();

        scalAbsoluteTolerance = absoluteTolerance;
        scalRelativeTolerance = relativeTolerance;
        vecAbsoluteTolerance  = null;
        vecRelativeTolerance  = null;

    }

    /** Set the adaptive step size control parameters.
     * <p>
     * A side effect of this method is to also reset the initial
     * step so it will be automatically computed by the integrator
     * if {@link #setInitialStepSize(RealFieldElement) setInitialStepSize}
     * is not called by the user.
     * </p>
     * @param minimalStep minimal step (must be positive even for backward
     * integration), the last step can be smaller than this
     * @param maximalStep maximal step (must be positive even for backward
     * integration)
     * @param absoluteTolerance allowed absolute error
     * @param relativeTolerance allowed relative error
     */
    public void setStepSizeControl(final double minimalStep, final double maximalStep,
                                   final double[] absoluteTolerance,
                                   final double[] relativeTolerance) {

        minStep     = getField().getZero().add(FastMath.abs(minimalStep));
        maxStep     = getField().getZero().add(FastMath.abs(maximalStep));
        initialStep = getField().getOne().negate();

        scalAbsoluteTolerance = 0;
        scalRelativeTolerance = 0;
        vecAbsoluteTolerance  = absoluteTolerance.clone();
        vecRelativeTolerance  = relativeTolerance.clone();

    }

    /** Set the initial step size.
     * <p>This method allows the user to specify an initial positive
     * step size instead of letting the integrator guess it by
     * itself. If this method is not called before integration is
     * started, the initial step size will be estimated by the
     * integrator.</p>
     * @param initialStepSize initial step size to use (must be positive even
     * for backward integration ; providing a negative value or a value
     * outside of the min/max step interval will lead the integrator to
     * ignore the value and compute the initial step size by itself)
     */
    public void setInitialStepSize(final T initialStepSize) {
        if (initialStepSize.subtract(minStep).getReal() < 0 ||
            initialStepSize.subtract(maxStep).getReal() > 0) {
            initialStep = getField().getOne().negate();
        } else {
            initialStep = initialStepSize;
        }
    }

    /** {@inheritDoc} */
    @Override
    protected void sanityChecks(final FieldODEState<T> eqn, final T t)
        throws DimensionMismatchException, NumberIsTooSmallException {

        super.sanityChecks(eqn, t);

        mainSetDimension = eqn.getStateDimension();

        if (vecAbsoluteTolerance != null && vecAbsoluteTolerance.length != mainSetDimension) {
            throw new DimensionMismatchException(mainSetDimension, vecAbsoluteTolerance.length);
        }

        if (vecRelativeTolerance != null && vecRelativeTolerance.length != mainSetDimension) {
            throw new DimensionMismatchException(mainSetDimension, vecRelativeTolerance.length);
        }

    }

    /** Initialize the integration step.
     * @param forward forward integration indicator
     * @param order order of the method
     * @param scale scaling vector for the state vector (can be shorter than state vector)
     * @param state0 state at integration start time
     * @param mapper mapper for all the equations
     * @return first integration step
     * @exception MaxCountExceededException if the number of functions evaluations is exceeded
     * @exception DimensionMismatchException if arrays dimensions do not match equations settings
     */
    public T initializeStep(final boolean forward, final int order, final T[] scale,
                            final FieldODEStateAndDerivative<T> state0,
                            final FieldEquationsMapper<T> mapper)
        throws MaxCountExceededException, DimensionMismatchException {

        if (initialStep.getReal() > 0) {
            // use the user provided value
            return forward ? initialStep : initialStep.negate();
        }

        // very rough first guess : h = 0.01 * ||y/scale|| / ||y'/scale||
        // this guess will be used to perform an Euler step
        final T[] y0    = mapper.mapState(state0);
        final T[] yDot0 = mapper.mapDerivative(state0);
        T yOnScale2    = getField().getZero();
        T yDotOnScale2 = getField().getZero();
        for (int j = 0; j < scale.length; ++j) {
            final T ratio    = y0[j].divide(scale[j]);
            yOnScale2        = yOnScale2.add(ratio.multiply(ratio));
            final T ratioDot = yDot0[j].divide(scale[j]);
            yDotOnScale2     = yDotOnScale2.add(ratioDot.multiply(ratioDot));
        }

        T h = (yOnScale2.getReal() < 1.0e-10 || yDotOnScale2.getReal() < 1.0e-10) ?
              getField().getZero().add(1.0e-6) :
              yOnScale2.divide(yDotOnScale2).sqrt().multiply(0.01);
        if (! forward) {
            h = h.negate();
        }

        // perform an Euler step using the preceding rough guess
        final T[] y1 = MathArrays.buildArray(getField(), y0.length);
        for (int j = 0; j < y0.length; ++j) {
            y1[j] = y0[j].add(yDot0[j].multiply(h));
        }
        final T[] yDot1 = computeDerivatives(state0.getTime().add(h), y1);

        // estimate the second derivative of the solution
        T yDDotOnScale = getField().getZero();
        for (int j = 0; j < scale.length; ++j) {
            final T ratioDotDot = yDot1[j].subtract(yDot0[j]).divide(scale[j]);
            yDDotOnScale = yDDotOnScale.add(ratioDotDot.multiply(ratioDotDot));
        }
        yDDotOnScale = yDDotOnScale.sqrt().divide(h);

        // step size is computed such that
        // h^order * max (||y'/tol||, ||y''/tol||) = 0.01
        final T maxInv2 = MathUtils.max(yDotOnScale2.sqrt(), yDDotOnScale);
        final T h1 = maxInv2.getReal() < 1.0e-15 ?
                     MathUtils.max(getField().getZero().add(1.0e-6), h.abs().multiply(0.001)) :
                     maxInv2.multiply(100).reciprocal().pow(1.0 / order);
        h = MathUtils.min(h.abs().multiply(100), h1);
        h = MathUtils.max(h, state0.getTime().abs().multiply(1.0e-12));  // avoids cancellation when computing t1 - t0
        h = MathUtils.max(minStep, MathUtils.min(maxStep, h));
        if (! forward) {
            h = h.negate();
        }

        return h;

    }

    /** Filter the integration step.
     * @param h signed step
     * @param forward forward integration indicator
     * @param acceptSmall if true, steps smaller than the minimal value
     * are silently increased up to this value, if false such small
     * steps generate an exception
     * @return a bounded integration step (h if no bound is reach, or a bounded value)
     * @exception NumberIsTooSmallException if the step is too small and acceptSmall is false
     */
    protected T filterStep(final T h, final boolean forward, final boolean acceptSmall)
        throws NumberIsTooSmallException {

        T filteredH = h;
        if (h.abs().subtract(minStep).getReal() < 0) {
            if (acceptSmall) {
                filteredH = forward ? minStep : minStep.negate();
            } else {
                throw new NumberIsTooSmallException(LocalizedFormats.MINIMAL_STEPSIZE_REACHED_DURING_INTEGRATION,
                                                    h.abs().getReal(), minStep.getReal(), true);
            }
        }

        if (filteredH.subtract(maxStep).getReal() > 0) {
            filteredH = maxStep;
        } else if (filteredH.add(maxStep).getReal() < 0) {
            filteredH = maxStep.negate();
        }

        return filteredH;

    }

    /** Reset internal state to dummy values. */
    protected void resetInternalState() {
        setStepStart(null);
        setStepSize(minStep.multiply(maxStep).sqrt());
    }

    /** Get the minimal step.
     * @return minimal step
     */
    public T getMinStep() {
        return minStep;
    }

    /** Get the maximal step.
     * @return maximal step
     */
    public T getMaxStep() {
        return maxStep;
    }

}
