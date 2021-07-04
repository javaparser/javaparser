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
import org.apache.commons.math3.exception.NoBracketingException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.linear.Array2DRowFieldMatrix;
import org.apache.commons.math3.ode.FieldExpandableODE;
import org.apache.commons.math3.ode.FieldODEState;
import org.apache.commons.math3.ode.FieldODEStateAndDerivative;
import org.apache.commons.math3.ode.MultistepFieldIntegrator;


/** Base class for {@link AdamsBashforthFieldIntegrator Adams-Bashforth} and
 * {@link AdamsMoultonFieldIntegrator Adams-Moulton} integrators.
 * @param <T> the type of the field elements
 * @since 3.6
 */
public abstract class AdamsFieldIntegrator<T extends RealFieldElement<T>> extends MultistepFieldIntegrator<T> {

    /** Transformer. */
    private final AdamsNordsieckFieldTransformer<T> transformer;

    /**
     * Build an Adams integrator with the given order and step control parameters.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param nSteps number of steps of the method excluding the one being computed
     * @param order order of the method
     * @param minStep minimal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param maxStep maximal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param scalAbsoluteTolerance allowed absolute error
     * @param scalRelativeTolerance allowed relative error
     * @exception NumberIsTooSmallException if order is 1 or less
     */
    public AdamsFieldIntegrator(final Field<T> field, final String name,
                                final int nSteps, final int order,
                                final double minStep, final double maxStep,
                                final double scalAbsoluteTolerance,
                                final double scalRelativeTolerance)
        throws NumberIsTooSmallException {
        super(field, name, nSteps, order, minStep, maxStep,
              scalAbsoluteTolerance, scalRelativeTolerance);
        transformer = AdamsNordsieckFieldTransformer.getInstance(field, nSteps);
    }

    /**
     * Build an Adams integrator with the given order and step control parameters.
     * @param field field to which the time and state vector elements belong
     * @param name name of the method
     * @param nSteps number of steps of the method excluding the one being computed
     * @param order order of the method
     * @param minStep minimal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param maxStep maximal step (sign is irrelevant, regardless of
     * integration direction, forward or backward), the last step can
     * be smaller than this
     * @param vecAbsoluteTolerance allowed absolute error
     * @param vecRelativeTolerance allowed relative error
     * @exception IllegalArgumentException if order is 1 or less
     */
    public AdamsFieldIntegrator(final Field<T> field, final String name,
                                final int nSteps, final int order,
                                final double minStep, final double maxStep,
                                final double[] vecAbsoluteTolerance,
                                final double[] vecRelativeTolerance)
        throws IllegalArgumentException {
        super(field, name, nSteps, order, minStep, maxStep,
              vecAbsoluteTolerance, vecRelativeTolerance);
        transformer = AdamsNordsieckFieldTransformer.getInstance(field, nSteps);
    }

    /** {@inheritDoc} */
    public abstract FieldODEStateAndDerivative<T> integrate(final FieldExpandableODE<T> equations,
                                                            final FieldODEState<T> initialState,
                                                            final T finalTime)
        throws NumberIsTooSmallException, DimensionMismatchException,
               MaxCountExceededException, NoBracketingException;

    /** {@inheritDoc} */
    @Override
    protected Array2DRowFieldMatrix<T> initializeHighOrderDerivatives(final T h, final T[] t,
                                                                      final T[][] y,
                                                                      final T[][] yDot) {
        return transformer.initializeHighOrderDerivatives(h, t, y, yDot);
    }

    /** Update the high order scaled derivatives for Adams integrators (phase 1).
     * <p>The complete update of high order derivatives has a form similar to:
     * <pre>
     * r<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub>
     * </pre>
     * this method computes the P<sup>-1</sup> A P r<sub>n</sub> part.</p>
     * @param highOrder high order scaled derivatives
     * (h<sup>2</sup>/2 y'', ... h<sup>k</sup>/k! y(k))
     * @return updated high order derivatives
     * @see #updateHighOrderDerivativesPhase2(RealFieldElement[], RealFieldElement[], Array2DRowFieldMatrix)
     */
    public Array2DRowFieldMatrix<T> updateHighOrderDerivativesPhase1(final Array2DRowFieldMatrix<T> highOrder) {
        return transformer.updateHighOrderDerivativesPhase1(highOrder);
    }

    /** Update the high order scaled derivatives Adams integrators (phase 2).
     * <p>The complete update of high order derivatives has a form similar to:
     * <pre>
     * r<sub>n+1</sub> = (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u + P<sup>-1</sup> A P r<sub>n</sub>
     * </pre>
     * this method computes the (s<sub>1</sub>(n) - s<sub>1</sub>(n+1)) P<sup>-1</sup> u part.</p>
     * <p>Phase 1 of the update must already have been performed.</p>
     * @param start first order scaled derivatives at step start
     * @param end first order scaled derivatives at step end
     * @param highOrder high order scaled derivatives, will be modified
     * (h<sup>2</sup>/2 y'', ... h<sup>k</sup>/k! y(k))
     * @see #updateHighOrderDerivativesPhase1(Array2DRowFieldMatrix)
     */
    public void updateHighOrderDerivativesPhase2(final T[] start, final T[] end,
                                                 final Array2DRowFieldMatrix<T> highOrder) {
        transformer.updateHighOrderDerivativesPhase2(start, end, highOrder);
    }

}
