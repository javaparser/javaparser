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
package org.apache.commons.math3.optim.linear;

import java.util.ArrayList;
import java.util.List;

import org.apache.commons.math3.exception.TooManyIterationsException;
import org.apache.commons.math3.optim.OptimizationData;
import org.apache.commons.math3.optim.PointValuePair;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * Solves a linear problem using the "Two-Phase Simplex" method.
 * <p>
 * The {@link SimplexSolver} supports the following {@link OptimizationData} data provided
 * as arguments to {@link #optimize(OptimizationData...)}:
 * <ul>
 *   <li>objective function: {@link LinearObjectiveFunction} - mandatory</li>
 *   <li>linear constraints {@link LinearConstraintSet} - mandatory</li>
 *   <li>type of optimization: {@link org.apache.commons.math3.optim.nonlinear.scalar.GoalType GoalType}
 *    - optional, default: {@link org.apache.commons.math3.optim.nonlinear.scalar.GoalType#MINIMIZE MINIMIZE}</li>
 *   <li>whether to allow negative values as solution: {@link NonNegativeConstraint} - optional, default: true</li>
 *   <li>pivot selection rule: {@link PivotSelectionRule} - optional, default {@link PivotSelectionRule#DANTZIG}</li>
 *   <li>callback for the best solution: {@link SolutionCallback} - optional</li>
 *   <li>maximum number of iterations: {@link org.apache.commons.math3.optim.MaxIter} - optional, default: {@link Integer#MAX_VALUE}</li>
 * </ul>
 * <p>
 * <b>Note:</b> Depending on the problem definition, the default convergence criteria
 * may be too strict, resulting in {@link NoFeasibleSolutionException} or
 * {@link TooManyIterationsException}. In such a case it is advised to adjust these
 * criteria with more appropriate values, e.g. relaxing the epsilon value.
 * <p>
 * Default convergence criteria:
 * <ul>
 *   <li>Algorithm convergence: 1e-6</li>
 *   <li>Floating-point comparisons: 10 ulp</li>
 *   <li>Cut-Off value: 1e-10</li>
  * </ul>
 * <p>
 * The cut-off value has been introduced to handle the case of very small pivot elements
 * in the Simplex tableau, as these may lead to numerical instabilities and degeneracy.
 * Potential pivot elements smaller than this value will be treated as if they were zero
 * and are thus not considered by the pivot selection mechanism. The default value is safe
 * for many problems, but may need to be adjusted in case of very small coefficients
 * used in either the {@link LinearConstraint} or {@link LinearObjectiveFunction}.
 *
 * @since 2.0
 */
public class SimplexSolver extends LinearOptimizer {
    /** Default amount of error to accept in floating point comparisons (as ulps). */
    static final int DEFAULT_ULPS = 10;

    /** Default cut-off value. */
    static final double DEFAULT_CUT_OFF = 1e-10;

    /** Default amount of error to accept for algorithm convergence. */
    private static final double DEFAULT_EPSILON = 1.0e-6;

    /** Amount of error to accept for algorithm convergence. */
    private final double epsilon;

    /** Amount of error to accept in floating point comparisons (as ulps). */
    private final int maxUlps;

    /**
     * Cut-off value for entries in the tableau: values smaller than the cut-off
     * are treated as zero to improve numerical stability.
     */
    private final double cutOff;

    /** The pivot selection method to use. */
    private PivotSelectionRule pivotSelection;

    /**
     * The solution callback to access the best solution found so far in case
     * the optimizer fails to find an optimal solution within the iteration limits.
     */
    private SolutionCallback solutionCallback;

    /**
     * Builds a simplex solver with default settings.
     */
    public SimplexSolver() {
        this(DEFAULT_EPSILON, DEFAULT_ULPS, DEFAULT_CUT_OFF);
    }

    /**
     * Builds a simplex solver with a specified accepted amount of error.
     *
     * @param epsilon Amount of error to accept for algorithm convergence.
     */
    public SimplexSolver(final double epsilon) {
        this(epsilon, DEFAULT_ULPS, DEFAULT_CUT_OFF);
    }

    /**
     * Builds a simplex solver with a specified accepted amount of error.
     *
     * @param epsilon Amount of error to accept for algorithm convergence.
     * @param maxUlps Amount of error to accept in floating point comparisons.
     */
    public SimplexSolver(final double epsilon, final int maxUlps) {
        this(epsilon, maxUlps, DEFAULT_CUT_OFF);
    }

    /**
     * Builds a simplex solver with a specified accepted amount of error.
     *
     * @param epsilon Amount of error to accept for algorithm convergence.
     * @param maxUlps Amount of error to accept in floating point comparisons.
     * @param cutOff Values smaller than the cutOff are treated as zero.
     */
    public SimplexSolver(final double epsilon, final int maxUlps, final double cutOff) {
        this.epsilon = epsilon;
        this.maxUlps = maxUlps;
        this.cutOff = cutOff;
        this.pivotSelection = PivotSelectionRule.DANTZIG;
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data. In addition to those documented in
     * {@link LinearOptimizer#optimize(OptimizationData...)
     * LinearOptimizer}, this method will register the following data:
     * <ul>
     *  <li>{@link SolutionCallback}</li>
     *  <li>{@link PivotSelectionRule}</li>
     * </ul>
     *
     * @return {@inheritDoc}
     * @throws TooManyIterationsException if the maximal number of iterations is exceeded.
     */
    @Override
    public PointValuePair optimize(OptimizationData... optData)
        throws TooManyIterationsException {
        // Set up base class and perform computation.
        return super.optimize(optData);
    }

    /**
     * {@inheritDoc}
     *
     * @param optData Optimization data.
     * In addition to those documented in
     * {@link LinearOptimizer#parseOptimizationData(OptimizationData[])
     * LinearOptimizer}, this method will register the following data:
     * <ul>
     *  <li>{@link SolutionCallback}</li>
     *  <li>{@link PivotSelectionRule}</li>
     * </ul>
     */
    @Override
    protected void parseOptimizationData(OptimizationData... optData) {
        // Allow base class to register its own data.
        super.parseOptimizationData(optData);

        // reset the callback before parsing
        solutionCallback = null;

        for (OptimizationData data : optData) {
            if (data instanceof SolutionCallback) {
                solutionCallback = (SolutionCallback) data;
                continue;
            }
            if (data instanceof PivotSelectionRule) {
                pivotSelection = (PivotSelectionRule) data;
                continue;
            }
        }
    }

    /**
     * Returns the column with the most negative coefficient in the objective function row.
     *
     * @param tableau Simple tableau for the problem.
     * @return the column with the most negative coefficient.
     */
    private Integer getPivotColumn(SimplexTableau tableau) {
        double minValue = 0;
        Integer minPos = null;
        for (int i = tableau.getNumObjectiveFunctions(); i < tableau.getWidth() - 1; i++) {
            final double entry = tableau.getEntry(0, i);
            // check if the entry is strictly smaller than the current minimum
            // do not use a ulp/epsilon check
            if (entry < minValue) {
                minValue = entry;
                minPos = i;

                // Bland's rule: chose the entering column with the lowest index
                if (pivotSelection == PivotSelectionRule.BLAND && isValidPivotColumn(tableau, i)) {
                    break;
                }
            }
        }
        return minPos;
    }

    /**
     * Checks whether the given column is valid pivot column, i.e. will result
     * in a valid pivot row.
     * <p>
     * When applying Bland's rule to select the pivot column, it may happen that
     * there is no corresponding pivot row. This method will check if the selected
     * pivot column will return a valid pivot row.
     *
     * @param tableau simplex tableau for the problem
     * @param col the column to test
     * @return {@code true} if the pivot column is valid, {@code false} otherwise
     */
    private boolean isValidPivotColumn(SimplexTableau tableau, int col) {
        for (int i = tableau.getNumObjectiveFunctions(); i < tableau.getHeight(); i++) {
            final double entry = tableau.getEntry(i, col);

            // do the same check as in getPivotRow
            if (Precision.compareTo(entry, 0d, cutOff) > 0) {
                return true;
            }
        }
        return false;
    }

    /**
     * Returns the row with the minimum ratio as given by the minimum ratio test (MRT).
     *
     * @param tableau Simplex tableau for the problem.
     * @param col Column to test the ratio of (see {@link #getPivotColumn(SimplexTableau)}).
     * @return the row with the minimum ratio.
     */
    private Integer getPivotRow(SimplexTableau tableau, final int col) {
        // create a list of all the rows that tie for the lowest score in the minimum ratio test
        List<Integer> minRatioPositions = new ArrayList<Integer>();
        double minRatio = Double.MAX_VALUE;
        for (int i = tableau.getNumObjectiveFunctions(); i < tableau.getHeight(); i++) {
            final double rhs = tableau.getEntry(i, tableau.getWidth() - 1);
            final double entry = tableau.getEntry(i, col);

            // only consider pivot elements larger than the cutOff threshold
            // selecting others may lead to degeneracy or numerical instabilities
            if (Precision.compareTo(entry, 0d, cutOff) > 0) {
                final double ratio = FastMath.abs(rhs / entry);
                // check if the entry is strictly equal to the current min ratio
                // do not use a ulp/epsilon check
                final int cmp = Double.compare(ratio, minRatio);
                if (cmp == 0) {
                    minRatioPositions.add(i);
                } else if (cmp < 0) {
                    minRatio = ratio;
                    minRatioPositions.clear();
                    minRatioPositions.add(i);
                }
            }
        }

        if (minRatioPositions.size() == 0) {
            return null;
        } else if (minRatioPositions.size() > 1) {
            // there's a degeneracy as indicated by a tie in the minimum ratio test

            // 1. check if there's an artificial variable that can be forced out of the basis
            if (tableau.getNumArtificialVariables() > 0) {
                for (Integer row : minRatioPositions) {
                    for (int i = 0; i < tableau.getNumArtificialVariables(); i++) {
                        int column = i + tableau.getArtificialVariableOffset();
                        final double entry = tableau.getEntry(row, column);
                        if (Precision.equals(entry, 1d, maxUlps) && row.equals(tableau.getBasicRow(column))) {
                            return row;
                        }
                    }
                }
            }

            // 2. apply Bland's rule to prevent cycling:
            //    take the row for which the corresponding basic variable has the smallest index
            //
            // see http://www.stanford.edu/class/msande310/blandrule.pdf
            // see http://en.wikipedia.org/wiki/Bland%27s_rule (not equivalent to the above paper)

            Integer minRow = null;
            int minIndex = tableau.getWidth();
            for (Integer row : minRatioPositions) {
                final int basicVar = tableau.getBasicVariable(row);
                if (basicVar < minIndex) {
                    minIndex = basicVar;
                    minRow = row;
                }
            }
            return minRow;
        }
        return minRatioPositions.get(0);
    }

    /**
     * Runs one iteration of the Simplex method on the given model.
     *
     * @param tableau Simple tableau for the problem.
     * @throws TooManyIterationsException if the allowed number of iterations has been exhausted.
     * @throws UnboundedSolutionException if the model is found not to have a bounded solution.
     */
    protected void doIteration(final SimplexTableau tableau)
        throws TooManyIterationsException,
               UnboundedSolutionException {

        incrementIterationCount();

        Integer pivotCol = getPivotColumn(tableau);
        Integer pivotRow = getPivotRow(tableau, pivotCol);
        if (pivotRow == null) {
            throw new UnboundedSolutionException();
        }

        tableau.performRowOperations(pivotCol, pivotRow);
    }

    /**
     * Solves Phase 1 of the Simplex method.
     *
     * @param tableau Simple tableau for the problem.
     * @throws TooManyIterationsException if the allowed number of iterations has been exhausted.
     * @throws UnboundedSolutionException if the model is found not to have a bounded solution.
     * @throws NoFeasibleSolutionException if there is no feasible solution?
     */
    protected void solvePhase1(final SimplexTableau tableau)
        throws TooManyIterationsException,
               UnboundedSolutionException,
               NoFeasibleSolutionException {

        // make sure we're in Phase 1
        if (tableau.getNumArtificialVariables() == 0) {
            return;
        }

        while (!tableau.isOptimal()) {
            doIteration(tableau);
        }

        // if W is not zero then we have no feasible solution
        if (!Precision.equals(tableau.getEntry(0, tableau.getRhsOffset()), 0d, epsilon)) {
            throw new NoFeasibleSolutionException();
        }
    }

    /** {@inheritDoc} */
    @Override
    public PointValuePair doOptimize()
        throws TooManyIterationsException,
               UnboundedSolutionException,
               NoFeasibleSolutionException {

        // reset the tableau to indicate a non-feasible solution in case
        // we do not pass phase 1 successfully
        if (solutionCallback != null) {
            solutionCallback.setTableau(null);
        }

        final SimplexTableau tableau =
            new SimplexTableau(getFunction(),
                               getConstraints(),
                               getGoalType(),
                               isRestrictedToNonNegative(),
                               epsilon,
                               maxUlps);

        solvePhase1(tableau);
        tableau.dropPhase1Objective();

        // after phase 1, we are sure to have a feasible solution
        if (solutionCallback != null) {
            solutionCallback.setTableau(tableau);
        }

        while (!tableau.isOptimal()) {
            doIteration(tableau);
        }

        // check that the solution respects the nonNegative restriction in case
        // the epsilon/cutOff values are too large for the actual linear problem
        // (e.g. with very small constraint coefficients), the solver might actually
        // find a non-valid solution (with negative coefficients).
        final PointValuePair solution = tableau.getSolution();
        if (isRestrictedToNonNegative()) {
            final double[] coeff = solution.getPoint();
            for (int i = 0; i < coeff.length; i++) {
                if (Precision.compareTo(coeff[i], 0, epsilon) < 0) {
                    throw new NoFeasibleSolutionException();
                }
            }
        }
        return solution;
    }
}
