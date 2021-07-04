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

import java.lang.reflect.Array;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MaxCountExceededException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * This class defines a set of {@link SecondaryEquations secondary equations} to
 * compute the Jacobian matrices with respect to the initial state vector and, if
 * any, to some parameters of the primary ODE set.
 * <p>
 * It is intended to be packed into an {@link ExpandableStatefulODE}
 * in conjunction with a primary set of ODE, which may be:
 * <ul>
 * <li>a {@link FirstOrderDifferentialEquations}</li>
 * <li>a {@link MainStateJacobianProvider}</li>
 * </ul>
 * In order to compute Jacobian matrices with respect to some parameters of the
 * primary ODE set, the following parameter Jacobian providers may be set:
 * <ul>
 * <li>a {@link ParameterJacobianProvider}</li>
 * <li>a {@link ParameterizedODE}</li>
 * </ul>
 * </p>
 *
 * @see ExpandableStatefulODE
 * @see FirstOrderDifferentialEquations
 * @see MainStateJacobianProvider
 * @see ParameterJacobianProvider
 * @see ParameterizedODE
 *
 * @since 3.0
 */
public class JacobianMatrices {

    /** Expandable first order differential equation. */
    private ExpandableStatefulODE efode;

    /** Index of the instance in the expandable set. */
    private int index;

    /** FODE with exact primary Jacobian computation skill. */
    private MainStateJacobianProvider jode;

    /** FODE without exact parameter Jacobian computation skill. */
    private ParameterizedODE pode;

    /** Main state vector dimension. */
    private int stateDim;

    /** Selected parameters for parameter Jacobian computation. */
    private ParameterConfiguration[] selectedParameters;

    /** FODE with exact parameter Jacobian computation skill. */
    private List<ParameterJacobianProvider> jacobianProviders;

    /** Parameters dimension. */
    private int paramDim;

    /** Boolean for selected parameters consistency. */
    private boolean dirtyParameter;

    /** State and parameters Jacobian matrices in a row. */
    private double[] matricesData;

    /** Simple constructor for a secondary equations set computing Jacobian matrices.
     * <p>
     * Parameters must belong to the supported ones given by {@link
     * Parameterizable#getParametersNames()}, so the primary set of differential
     * equations must be {@link Parameterizable}.
     * </p>
     * <p>Note that each selection clears the previous selected parameters.</p>
     *
     * @param fode the primary first order differential equations set to extend
     * @param hY step used for finite difference computation with respect to state vector
     * @param parameters parameters to consider for Jacobian matrices processing
     * (may be null if parameters Jacobians is not desired)
     * @exception DimensionMismatchException if there is a dimension mismatch between
     * the steps array {@code hY} and the equation dimension
     */
    public JacobianMatrices(final FirstOrderDifferentialEquations fode, final double[] hY,
                            final String... parameters)
        throws DimensionMismatchException {
        this(new MainStateJacobianWrapper(fode, hY), parameters);
    }

    /** Simple constructor for a secondary equations set computing Jacobian matrices.
     * <p>
     * Parameters must belong to the supported ones given by {@link
     * Parameterizable#getParametersNames()}, so the primary set of differential
     * equations must be {@link Parameterizable}.
     * </p>
     * <p>Note that each selection clears the previous selected parameters.</p>
     *
     * @param jode the primary first order differential equations set to extend
     * @param parameters parameters to consider for Jacobian matrices processing
     * (may be null if parameters Jacobians is not desired)
     */
    public JacobianMatrices(final MainStateJacobianProvider jode,
                            final String... parameters) {

        this.efode = null;
        this.index = -1;

        this.jode = jode;
        this.pode = null;

        this.stateDim = jode.getDimension();

        if (parameters == null) {
            selectedParameters = null;
            paramDim = 0;
        } else {
            this.selectedParameters = new ParameterConfiguration[parameters.length];
            for (int i = 0; i < parameters.length; ++i) {
                selectedParameters[i] = new ParameterConfiguration(parameters[i], Double.NaN);
            }
            paramDim = parameters.length;
        }
        this.dirtyParameter = false;

        this.jacobianProviders = new ArrayList<ParameterJacobianProvider>();

        // set the default initial state Jacobian to the identity
        // and the default initial parameters Jacobian to the null matrix
        matricesData = new double[(stateDim + paramDim) * stateDim];
        for (int i = 0; i < stateDim; ++i) {
            matricesData[i * (stateDim + 1)] = 1.0;
        }

    }

    /** Register the variational equations for the Jacobians matrices to the expandable set.
     * @param expandable expandable set into which variational equations should be registered
     * @throws DimensionMismatchException if the dimension of the partial state does not
     * match the selected equations set dimension
     * @exception MismatchedEquations if the primary set of the expandable set does
     * not match the one used to build the instance
     * @see ExpandableStatefulODE#addSecondaryEquations(SecondaryEquations)
     */
    public void registerVariationalEquations(final ExpandableStatefulODE expandable)
        throws DimensionMismatchException, MismatchedEquations {

        // safety checks
        final FirstOrderDifferentialEquations ode = (jode instanceof MainStateJacobianWrapper) ?
                                                    ((MainStateJacobianWrapper) jode).ode :
                                                    jode;
        if (expandable.getPrimary() != ode) {
            throw new MismatchedEquations();
        }

        efode = expandable;
        index = efode.addSecondaryEquations(new JacobiansSecondaryEquations());
        efode.setSecondaryState(index, matricesData);

    }

    /** Add a parameter Jacobian provider.
     * @param provider the parameter Jacobian provider to compute exactly the parameter Jacobian matrix
     */
    public void addParameterJacobianProvider(final ParameterJacobianProvider provider) {
        jacobianProviders.add(provider);
    }

    /** Set a parameter Jacobian provider.
     * @param parameterizedOde the parameterized ODE to compute the parameter Jacobian matrix using finite differences
     */
    public void setParameterizedODE(final ParameterizedODE parameterizedOde) {
        this.pode = parameterizedOde;
        dirtyParameter = true;
    }

    /** Set the step associated to a parameter in order to compute by finite
     *  difference the Jacobian matrix.
     * <p>
     * Needed if and only if the primary ODE set is a {@link ParameterizedODE}.
     * </p>
     * <p>
     * Given a non zero parameter value pval for the parameter, a reasonable value
     * for such a step is {@code pval * FastMath.sqrt(Precision.EPSILON)}.
     * </p>
     * <p>
     * A zero value for such a step doesn't enable to compute the parameter Jacobian matrix.
     * </p>
     * @param parameter parameter to consider for Jacobian processing
     * @param hP step for Jacobian finite difference computation w.r.t. the specified parameter
     * @see ParameterizedODE
     * @exception UnknownParameterException if the parameter is not supported
     */
    public void setParameterStep(final String parameter, final double hP)
        throws UnknownParameterException {

        for (ParameterConfiguration param: selectedParameters) {
            if (parameter.equals(param.getParameterName())) {
                param.setHP(hP);
                dirtyParameter = true;
                return;
            }
        }

        throw new UnknownParameterException(parameter);

    }

    /** Set the initial value of the Jacobian matrix with respect to state.
     * <p>
     * If this method is not called, the initial value of the Jacobian
     * matrix with respect to state is set to identity.
     * </p>
     * @param dYdY0 initial Jacobian matrix w.r.t. state
     * @exception DimensionMismatchException if matrix dimensions are incorrect
     */
    public void setInitialMainStateJacobian(final double[][] dYdY0)
        throws DimensionMismatchException {

        // Check dimensions
        checkDimension(stateDim, dYdY0);
        checkDimension(stateDim, dYdY0[0]);

        // store the matrix in row major order as a single dimension array
        int i = 0;
        for (final double[] row : dYdY0) {
            System.arraycopy(row, 0, matricesData, i, stateDim);
            i += stateDim;
        }

        if (efode != null) {
            efode.setSecondaryState(index, matricesData);
        }

    }

    /** Set the initial value of a column of the Jacobian matrix with respect to one parameter.
     * <p>
     * If this method is not called for some parameter, the initial value of
     * the column of the Jacobian matrix with respect to this parameter is set to zero.
     * </p>
     * @param pName parameter name
     * @param dYdP initial Jacobian column vector with respect to the parameter
     * @exception UnknownParameterException if a parameter is not supported
     * @throws DimensionMismatchException if the column vector does not match state dimension
     */
    public void setInitialParameterJacobian(final String pName, final double[] dYdP)
        throws UnknownParameterException, DimensionMismatchException {

        // Check dimensions
        checkDimension(stateDim, dYdP);

        // store the column in a global single dimension array
        int i = stateDim * stateDim;
        for (ParameterConfiguration param: selectedParameters) {
            if (pName.equals(param.getParameterName())) {
                System.arraycopy(dYdP, 0, matricesData, i, stateDim);
                if (efode != null) {
                    efode.setSecondaryState(index, matricesData);
                }
                return;
            }
            i += stateDim;
        }

        throw new UnknownParameterException(pName);

    }

    /** Get the current value of the Jacobian matrix with respect to state.
     * @param dYdY0 current Jacobian matrix with respect to state.
     */
    public void getCurrentMainSetJacobian(final double[][] dYdY0) {

        // get current state for this set of equations from the expandable fode
        double[] p = efode.getSecondaryState(index);

        int j = 0;
        for (int i = 0; i < stateDim; i++) {
            System.arraycopy(p, j, dYdY0[i], 0, stateDim);
            j += stateDim;
        }

    }

    /** Get the current value of the Jacobian matrix with respect to one parameter.
     * @param pName name of the parameter for the computed Jacobian matrix
     * @param dYdP current Jacobian matrix with respect to the named parameter
     */
    public void getCurrentParameterJacobian(String pName, final double[] dYdP) {

        // get current state for this set of equations from the expandable fode
        double[] p = efode.getSecondaryState(index);

        int i = stateDim * stateDim;
        for (ParameterConfiguration param: selectedParameters) {
            if (param.getParameterName().equals(pName)) {
                System.arraycopy(p, i, dYdP, 0, stateDim);
                return;
            }
            i += stateDim;
        }

    }

    /** Check array dimensions.
     * @param expected expected dimension
     * @param array (may be null if expected is 0)
     * @throws DimensionMismatchException if the array dimension does not match the expected one
     */
    private void checkDimension(final int expected, final Object array)
        throws DimensionMismatchException {
        int arrayDimension = (array == null) ? 0 : Array.getLength(array);
        if (arrayDimension != expected) {
            throw new DimensionMismatchException(arrayDimension, expected);
        }
    }

    /** Local implementation of secondary equations.
     * <p>
     * This class is an inner class to ensure proper scheduling of calls
     * by forcing the use of {@link JacobianMatrices#registerVariationalEquations(ExpandableStatefulODE)}.
     * </p>
     */
    private class JacobiansSecondaryEquations implements SecondaryEquations {

        /** {@inheritDoc} */
        public int getDimension() {
            return stateDim * (stateDim + paramDim);
        }

        /** {@inheritDoc} */
        public void computeDerivatives(final double t, final double[] y, final double[] yDot,
                                       final double[] z, final double[] zDot)
            throws MaxCountExceededException, DimensionMismatchException {

            // Lazy initialization
            if (dirtyParameter && (paramDim != 0)) {
                jacobianProviders.add(new ParameterJacobianWrapper(jode, pode, selectedParameters));
                dirtyParameter = false;
            }

            // variational equations:
            // from d[dy/dt]/dy0 and d[dy/dt]/dp to d[dy/dy0]/dt and d[dy/dp]/dt

            // compute Jacobian matrix with respect to primary state
            double[][] dFdY = new double[stateDim][stateDim];
            jode.computeMainStateJacobian(t, y, yDot, dFdY);

            // Dispatch Jacobian matrix in the compound secondary state vector
            for (int i = 0; i < stateDim; ++i) {
                final double[] dFdYi = dFdY[i];
                for (int j = 0; j < stateDim; ++j) {
                    double s = 0;
                    final int startIndex = j;
                    int zIndex = startIndex;
                    for (int l = 0; l < stateDim; ++l) {
                        s += dFdYi[l] * z[zIndex];
                        zIndex += stateDim;
                    }
                    zDot[startIndex + i * stateDim] = s;
                }
            }

            if (paramDim != 0) {
                // compute Jacobian matrices with respect to parameters
                double[] dFdP = new double[stateDim];
                int startIndex = stateDim * stateDim;
                for (ParameterConfiguration param: selectedParameters) {
                    boolean found = false;
                    for (int k = 0 ; (!found) && (k < jacobianProviders.size()); ++k) {
                        final ParameterJacobianProvider provider = jacobianProviders.get(k);
                        if (provider.isSupported(param.getParameterName())) {
                            provider.computeParameterJacobian(t, y, yDot,
                                                              param.getParameterName(), dFdP);
                            for (int i = 0; i < stateDim; ++i) {
                                final double[] dFdYi = dFdY[i];
                                int zIndex = startIndex;
                                double s = dFdP[i];
                                for (int l = 0; l < stateDim; ++l) {
                                    s += dFdYi[l] * z[zIndex];
                                    zIndex++;
                                }
                                zDot[startIndex + i] = s;
                            }
                            found = true;
                        }
                    }
                    if (! found) {
                        Arrays.fill(zDot, startIndex, startIndex + stateDim, 0.0);
                    }
                    startIndex += stateDim;
                }
            }

        }
    }

    /** Wrapper class to compute jacobian matrices by finite differences for ODE
     *  which do not compute them by themselves.
     */
    private static class MainStateJacobianWrapper implements MainStateJacobianProvider {

        /** Raw ODE without jacobians computation skill to be wrapped into a MainStateJacobianProvider. */
        private final FirstOrderDifferentialEquations ode;

        /** Steps for finite difference computation of the jacobian df/dy w.r.t. state. */
        private final double[] hY;

        /** Wrap a {@link FirstOrderDifferentialEquations} into a {@link MainStateJacobianProvider}.
         * @param ode original ODE problem, without jacobians computation skill
         * @param hY step sizes to compute the jacobian df/dy
         * @exception DimensionMismatchException if there is a dimension mismatch between
         * the steps array {@code hY} and the equation dimension
         */
        MainStateJacobianWrapper(final FirstOrderDifferentialEquations ode,
                                 final double[] hY)
            throws DimensionMismatchException {
            this.ode = ode;
            this.hY = hY.clone();
            if (hY.length != ode.getDimension()) {
                throw new DimensionMismatchException(ode.getDimension(), hY.length);
            }
        }

        /** {@inheritDoc} */
        public int getDimension() {
            return ode.getDimension();
        }

        /** {@inheritDoc} */
        public void computeDerivatives(double t, double[] y, double[] yDot)
            throws MaxCountExceededException, DimensionMismatchException {
            ode.computeDerivatives(t, y, yDot);
        }

        /** {@inheritDoc} */
        public void computeMainStateJacobian(double t, double[] y, double[] yDot, double[][] dFdY)
            throws MaxCountExceededException, DimensionMismatchException {

            final int n = ode.getDimension();
            final double[] tmpDot = new double[n];

            for (int j = 0; j < n; ++j) {
                final double savedYj = y[j];
                y[j] += hY[j];
                ode.computeDerivatives(t, y, tmpDot);
                for (int i = 0; i < n; ++i) {
                    dFdY[i][j] = (tmpDot[i] - yDot[i]) / hY[j];
                }
                y[j] = savedYj;
            }
        }

    }

    /**
     * Special exception for equations mismatch.
     * @since 3.1
     */
    public static class MismatchedEquations extends MathIllegalArgumentException {

        /** Serializable UID. */
        private static final long serialVersionUID = 20120902L;

        /** Simple constructor. */
        public MismatchedEquations() {
            super(LocalizedFormats.UNMATCHED_ODE_IN_EXPANDED_SET);
        }

    }

}

