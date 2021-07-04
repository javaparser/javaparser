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

package org.apache.commons.math3.optimization.linear;

import java.util.Collection;

import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.PointValuePair;

/**
 * This interface represents an optimization algorithm for linear problems.
 * <p>Optimization algorithms find the input point set that either {@link GoalType
 * maximize or minimize} an objective function. In the linear case the form of
 * the function is restricted to
 * <pre>
 * c<sub>1</sub>x<sub>1</sub> + ... c<sub>n</sub>x<sub>n</sub> = v
 * </pre>
 * and there may be linear constraints too, of one of the forms:
 * <ul>
 *   <li>c<sub>1</sub>x<sub>1</sub> + ... c<sub>n</sub>x<sub>n</sub> = v</li>
 *   <li>c<sub>1</sub>x<sub>1</sub> + ... c<sub>n</sub>x<sub>n</sub> &lt;= v</li>
 *   <li>c<sub>1</sub>x<sub>1</sub> + ... c<sub>n</sub>x<sub>n</sub> >= v</li>
 *   <li>l<sub>1</sub>x<sub>1</sub> + ... l<sub>n</sub>x<sub>n</sub> + l<sub>cst</sub> =
 *       r<sub>1</sub>x<sub>1</sub> + ... r<sub>n</sub>x<sub>n</sub> + r<sub>cst</sub></li>
 *   <li>l<sub>1</sub>x<sub>1</sub> + ... l<sub>n</sub>x<sub>n</sub> + l<sub>cst</sub> &lt;=
 *       r<sub>1</sub>x<sub>1</sub> + ... r<sub>n</sub>x<sub>n</sub> + r<sub>cst</sub></li>
 *   <li>l<sub>1</sub>x<sub>1</sub> + ... l<sub>n</sub>x<sub>n</sub> + l<sub>cst</sub> >=
 *       r<sub>1</sub>x<sub>1</sub> + ... r<sub>n</sub>x<sub>n</sub> + r<sub>cst</sub></li>
 * </ul>
 * where the c<sub>i</sub>, l<sub>i</sub> or r<sub>i</sub> are the coefficients of
 * the constraints, the x<sub>i</sub> are the coordinates of the current point and
 * v is the value of the constraint.
 * </p>
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.0
 */
@Deprecated
public interface LinearOptimizer {

    /**
     * Set the maximal number of iterations of the algorithm.
     * @param maxIterations maximal number of function calls
     */
    void setMaxIterations(int maxIterations);

    /**
     * Get the maximal number of iterations of the algorithm.
     * @return maximal number of iterations
     */
    int getMaxIterations();

    /**
     * Get the number of iterations realized by the algorithm.
     * <p>
     * The number of evaluations corresponds to the last call to the
     * {@link #optimize(LinearObjectiveFunction, Collection, GoalType, boolean) optimize}
     * method. It is 0 if the method has not been called yet.
     * </p>
     * @return number of iterations
     */
    int getIterations();

    /**
     * Optimizes an objective function.
     * @param f linear objective function
     * @param constraints linear constraints
     * @param goalType type of optimization goal: either {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}
     * @param restrictToNonNegative whether to restrict the variables to non-negative values
     * @return point/value pair giving the optimal value for objective function
     * @exception MathIllegalStateException if no solution fulfilling the constraints
     *   can be found in the allowed number of iterations
     */
   PointValuePair optimize(LinearObjectiveFunction f, Collection<LinearConstraint> constraints,
                               GoalType goalType, boolean restrictToNonNegative) throws MathIllegalStateException;

}
