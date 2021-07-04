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

import org.apache.commons.math3.RealFieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.MathArrays;

/**
 * Class mapping the part of a complete state or derivative that pertains
 * to a set of differential equations.
 * <p>
 * Instances of this class are guaranteed to be immutable.
 * </p>
 * @see FieldExpandableODE
 * @param <T> the type of the field elements
 * @since 3.6
 */
public class FieldEquationsMapper<T extends RealFieldElement<T>> implements Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 20151114L;

    /** Start indices of the components. */
    private final int[] start;

    /** Create a mapper by adding a new equation to another mapper.
     * <p>
     * The new equation will have index {@code mapper.}{@link #getNumberOfEquations()},
     * or 0 if {@code mapper} is null.
     * </p>
     * @param mapper former mapper, with one equation less (null for first equation)
     * @param dimension dimension of the equation state vector
     */
    FieldEquationsMapper(final FieldEquationsMapper<T> mapper, final int dimension) {
        final int index = (mapper == null) ? 0 : mapper.getNumberOfEquations();
        this.start = new int[index + 2];
        if (mapper == null) {
            start[0] = 0;
        } else {
            System.arraycopy(mapper.start, 0, start, 0, index + 1);
        }
        start[index + 1] = start[index] + dimension;
    }

    /** Get the number of equations mapped.
     * @return number of equations mapped
     */
    public int getNumberOfEquations() {
        return start.length - 1;
    }

    /** Return the dimension of the complete set of equations.
     * <p>
     * The complete set of equations correspond to the primary set plus all secondary sets.
     * </p>
     * @return dimension of the complete set of equations
     */
    public int getTotalDimension() {
        return start[start.length - 1];
    }

    /** Map a state to a complete flat array.
     * @param state state to map
     * @return flat array containing the mapped state, including primary and secondary components
     */
    public T[] mapState(final FieldODEState<T> state) {
        final T[] y = MathArrays.buildArray(state.getTime().getField(), getTotalDimension());
        int index = 0;
        insertEquationData(index, state.getState(), y);
        while (++index < getNumberOfEquations()) {
            insertEquationData(index, state.getSecondaryState(index), y);
        }
        return y;
    }

    /** Map a state derivative to a complete flat array.
     * @param state state to map
     * @return flat array containing the mapped state derivative, including primary and secondary components
     */
    public T[] mapDerivative(final FieldODEStateAndDerivative<T> state) {
        final T[] yDot = MathArrays.buildArray(state.getTime().getField(), getTotalDimension());
        int index = 0;
        insertEquationData(index, state.getDerivative(), yDot);
        while (++index < getNumberOfEquations()) {
            insertEquationData(index, state.getSecondaryDerivative(index), yDot);
        }
        return yDot;
    }

    /** Map flat arrays to a state and derivative.
     * @param t time
     * @param y state array to map, including primary and secondary components
     * @param yDot state derivative array to map, including primary and secondary components
     * @return mapped state
     * @exception DimensionMismatchException if an array does not match total dimension
     */
    public FieldODEStateAndDerivative<T> mapStateAndDerivative(final T t, final T[] y, final T[] yDot)
        throws DimensionMismatchException {

        if (y.length != getTotalDimension()) {
            throw new DimensionMismatchException(y.length, getTotalDimension());
        }

        if (yDot.length != getTotalDimension()) {
            throw new DimensionMismatchException(yDot.length, getTotalDimension());
        }

        final int n = getNumberOfEquations();
        int index = 0;
        final T[] state      = extractEquationData(index, y);
        final T[] derivative = extractEquationData(index, yDot);
        if (n < 2) {
            return new FieldODEStateAndDerivative<T>(t, state, derivative);
        } else {
            final T[][] secondaryState      = MathArrays.buildArray(t.getField(), n - 1, -1);
            final T[][] secondaryDerivative = MathArrays.buildArray(t.getField(), n - 1, -1);
            while (++index < getNumberOfEquations()) {
                secondaryState[index - 1]      = extractEquationData(index, y);
                secondaryDerivative[index - 1] = extractEquationData(index, yDot);
            }
            return new FieldODEStateAndDerivative<T>(t, state, derivative, secondaryState, secondaryDerivative);
        }
    }

    /** Extract equation data from a complete state or derivative array.
     * @param index index of the equation, must be between 0 included and
     * {@link #getNumberOfEquations()} (excluded)
     * @param complete complete state or derivative array from which
     * equation data should be retrieved
     * @return equation data
     * @exception MathIllegalArgumentException if index is out of range
     * @exception DimensionMismatchException if complete state has not enough elements
     */
    public T[] extractEquationData(final int index, final T[] complete)
        throws MathIllegalArgumentException, DimensionMismatchException {
        checkIndex(index);
        final int begin     = start[index];
        final int end       = start[index + 1];
        if (complete.length < end) {
            throw new DimensionMismatchException(complete.length, end);
        }
        final int dimension = end - begin;
        final T[] equationData = MathArrays.buildArray(complete[0].getField(), dimension);
        System.arraycopy(complete, begin, equationData, 0, dimension);
        return equationData;
    }

    /** Insert equation data into a complete state or derivative array.
     * @param index index of the equation, must be between 0 included and
     * {@link #getNumberOfEquations()} (excluded)
     * @param equationData equation data to be inserted into the complete array
     * @param complete placeholder where to put equation data (only the
     * part corresponding to the equation will be overwritten)
     * @exception DimensionMismatchException if either array has not enough elements
     */
    public void insertEquationData(final int index, T[] equationData, T[] complete)
        throws DimensionMismatchException {
        checkIndex(index);
        final int begin     = start[index];
        final int end       = start[index + 1];
        final int dimension = end - begin;
        if (complete.length < end) {
            throw new DimensionMismatchException(complete.length, end);
        }
        if (equationData.length != dimension) {
            throw new DimensionMismatchException(equationData.length, dimension);
        }
        System.arraycopy(equationData, 0, complete, begin, dimension);
    }

    /** Check equation index.
     * @param index index of the equation, must be between 0 included and
     * {@link #getNumberOfEquations()} (excluded)
     * @exception MathIllegalArgumentException if index is out of range
     */
    private void checkIndex(final int index) throws MathIllegalArgumentException {
        if (index < 0 || index > start.length - 2) {
            throw new MathIllegalArgumentException(LocalizedFormats.ARGUMENT_OUTSIDE_DOMAIN,
                                                   index, 0, start.length - 2);
        }
    }

}
