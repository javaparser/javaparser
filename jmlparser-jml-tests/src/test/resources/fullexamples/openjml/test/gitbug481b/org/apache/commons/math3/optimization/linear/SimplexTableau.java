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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import org.apache.commons.math3.linear.Array2DRowRealMatrix;
import org.apache.commons.math3.linear.MatrixUtils;
import org.apache.commons.math3.linear.RealMatrix;
import org.apache.commons.math3.linear.RealVector;
import org.apache.commons.math3.optimization.GoalType;
import org.apache.commons.math3.optimization.PointValuePair;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.Precision;

/**
 * A tableau for use in the Simplex method.
 *
 * <p>
 * Example:
 * <pre>
 *   W |  Z |  x1 |  x2 |  x- | s1 |  s2 |  a1 |  RHS
 * ---------------------------------------------------
 *  -1    0    0     0     0     0     0     1     0   &lt;= phase 1 objective
 *   0    1   -15   -10    0     0     0     0     0   &lt;= phase 2 objective
 *   0    0    1     0     0     1     0     0     2   &lt;= constraint 1
 *   0    0    0     1     0     0     1     0     3   &lt;= constraint 2
 *   0    0    1     1     0     0     0     1     4   &lt;= constraint 3
 * </pre>
 * W: Phase 1 objective function</br>
 * Z: Phase 2 objective function</br>
 * x1 &amp; x2: Decision variables</br>
 * x-: Extra decision variable to allow for negative values</br>
 * s1 &amp; s2: Slack/Surplus variables</br>
 * a1: Artificial variable</br>
 * RHS: Right hand side</br>
 * </p>
 * @deprecated As of 3.1 (to be removed in 4.0).
 * @since 2.0
 */
@Deprecated
class SimplexTableau implements Serializable {

    /** Column label for negative vars. */
    private static final String NEGATIVE_VAR_COLUMN_LABEL = "x-";

    /** Default amount of error to accept in floating point comparisons (as ulps). */
    private static final int DEFAULT_ULPS = 10;

    /** The cut-off threshold to zero-out entries. */
    private static final double CUTOFF_THRESHOLD = 1e-12;

    /** Serializable version identifier. */
    private static final long serialVersionUID = -1369660067587938365L;

    /** Linear objective function. */
    private final LinearObjectiveFunction f;

    /** Linear constraints. */
    private final List<LinearConstraint> constraints;

    /** Whether to restrict the variables to non-negative values. */
    private final boolean restrictToNonNegative;

    /** The variables each column represents */
    private final List<String> columnLabels = new ArrayList<String>();

    /** Simple tableau. */
    private transient RealMatrix tableau;

    /** Number of decision variables. */
    private final int numDecisionVariables;

    /** Number of slack variables. */
    private final int numSlackVariables;

    /** Number of artificial variables. */
    private int numArtificialVariables;

    /** Amount of error to accept when checking for optimality. */
    private final double epsilon;

    /** Amount of error to accept in floating point comparisons. */
    private final int maxUlps;

    /**
     * Build a tableau for a linear problem.
     * @param f linear objective function
     * @param constraints linear constraints
     * @param goalType type of optimization goal: either {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}
     * @param restrictToNonNegative whether to restrict the variables to non-negative values
     * @param epsilon amount of error to accept when checking for optimality
     */
    SimplexTableau(final LinearObjectiveFunction f,
                   final Collection<LinearConstraint> constraints,
                   final GoalType goalType, final boolean restrictToNonNegative,
                   final double epsilon) {
        this(f, constraints, goalType, restrictToNonNegative, epsilon, DEFAULT_ULPS);
    }

    /**
     * Build a tableau for a linear problem.
     * @param f linear objective function
     * @param constraints linear constraints
     * @param goalType type of optimization goal: either {@link GoalType#MAXIMIZE} or {@link GoalType#MINIMIZE}
     * @param restrictToNonNegative whether to restrict the variables to non-negative values
     * @param epsilon amount of error to accept when checking for optimality
     * @param maxUlps amount of error to accept in floating point comparisons
     */
    SimplexTableau(final LinearObjectiveFunction f,
                   final Collection<LinearConstraint> constraints,
                   final GoalType goalType, final boolean restrictToNonNegative,
                   final double epsilon,
                   final int maxUlps) {
        this.f                      = f;
        this.constraints            = normalizeConstraints(constraints);
        this.restrictToNonNegative  = restrictToNonNegative;
        this.epsilon                = epsilon;
        this.maxUlps                = maxUlps;
        this.numDecisionVariables   = f.getCoefficients().getDimension() +
                                      (restrictToNonNegative ? 0 : 1);
        this.numSlackVariables      = getConstraintTypeCounts(Relationship.LEQ) +
                                      getConstraintTypeCounts(Relationship.GEQ);
        this.numArtificialVariables = getConstraintTypeCounts(Relationship.EQ) +
                                      getConstraintTypeCounts(Relationship.GEQ);
        this.tableau = createTableau(goalType == GoalType.MAXIMIZE);
        initializeColumnLabels();
    }

    /**
     * Initialize the labels for the columns.
     */
    protected void initializeColumnLabels() {
      if (getNumObjectiveFunctions() == 2) {
        columnLabels.add("W");
      }
      columnLabels.add("Z");
      for (int i = 0; i < getOriginalNumDecisionVariables(); i++) {
        columnLabels.add("x" + i);
      }
      if (!restrictToNonNegative) {
        columnLabels.add(NEGATIVE_VAR_COLUMN_LABEL);
      }
      for (int i = 0; i < getNumSlackVariables(); i++) {
        columnLabels.add("s" + i);
      }
      for (int i = 0; i < getNumArtificialVariables(); i++) {
        columnLabels.add("a" + i);
      }
      columnLabels.add("RHS");
    }

    /**
     * Create the tableau by itself.
     * @param maximize if true, goal is to maximize the objective function
     * @return created tableau
     */
    protected RealMatrix createTableau(final boolean maximize) {

        // create a matrix of the correct size
        int width = numDecisionVariables + numSlackVariables +
        numArtificialVariables + getNumObjectiveFunctions() + 1; // + 1 is for RHS
        int height = constraints.size() + getNumObjectiveFunctions();
        Array2DRowRealMatrix matrix = new Array2DRowRealMatrix(height, width);

        // initialize the objective function rows
        if (getNumObjectiveFunctions() == 2) {
            matrix.setEntry(0, 0, -1);
        }
        int zIndex = (getNumObjectiveFunctions() == 1) ? 0 : 1;
        matrix.setEntry(zIndex, zIndex, maximize ? 1 : -1);
        RealVector objectiveCoefficients =
            maximize ? f.getCoefficients().mapMultiply(-1) : f.getCoefficients();
        copyArray(objectiveCoefficients.toArray(), matrix.getDataRef()[zIndex]);
        matrix.setEntry(zIndex, width - 1,
            maximize ? f.getConstantTerm() : -1 * f.getConstantTerm());

        if (!restrictToNonNegative) {
            matrix.setEntry(zIndex, getSlackVariableOffset() - 1,
                getInvertedCoefficientSum(objectiveCoefficients));
        }

        // initialize the constraint rows
        int slackVar = 0;
        int artificialVar = 0;
        for (int i = 0; i < constraints.size(); i++) {
            LinearConstraint constraint = constraints.get(i);
            int row = getNumObjectiveFunctions() + i;

            // decision variable coefficients
            copyArray(constraint.getCoefficients().toArray(), matrix.getDataRef()[row]);

            // x-
            if (!restrictToNonNegative) {
                matrix.setEntry(row, getSlackVariableOffset() - 1,
                    getInvertedCoefficientSum(constraint.getCoefficients()));
            }

            // RHS
            matrix.setEntry(row, width - 1, constraint.getValue());

            // slack variables
            if (constraint.getRelationship() == Relationship.LEQ) {
                matrix.setEntry(row, getSlackVariableOffset() + slackVar++, 1);  // slack
            } else if (constraint.getRelationship() == Relationship.GEQ) {
                matrix.setEntry(row, getSlackVariableOffset() + slackVar++, -1); // excess
            }

            // artificial variables
            if ((constraint.getRelationship() == Relationship.EQ) ||
                    (constraint.getRelationship() == Relationship.GEQ)) {
                matrix.setEntry(0, getArtificialVariableOffset() + artificialVar, 1);
                matrix.setEntry(row, getArtificialVariableOffset() + artificialVar++, 1);
                matrix.setRowVector(0, matrix.getRowVector(0).subtract(matrix.getRowVector(row)));
            }
        }

        return matrix;
    }

    /**
     * Get new versions of the constraints which have positive right hand sides.
     * @param originalConstraints original (not normalized) constraints
     * @return new versions of the constraints
     */
    public List<LinearConstraint> normalizeConstraints(Collection<LinearConstraint> originalConstraints) {
        List<LinearConstraint> normalized = new ArrayList<LinearConstraint>(originalConstraints.size());
        for (LinearConstraint constraint : originalConstraints) {
            normalized.add(normalize(constraint));
        }
        return normalized;
    }

    /**
     * Get a new equation equivalent to this one with a positive right hand side.
     * @param constraint reference constraint
     * @return new equation
     */
    private LinearConstraint normalize(final LinearConstraint constraint) {
        if (constraint.getValue() < 0) {
            return new LinearConstraint(constraint.getCoefficients().mapMultiply(-1),
                                        constraint.getRelationship().oppositeRelationship(),
                                        -1 * constraint.getValue());
        }
        return new LinearConstraint(constraint.getCoefficients(),
                                    constraint.getRelationship(), constraint.getValue());
    }

    /**
     * Get the number of objective functions in this tableau.
     * @return 2 for Phase 1.  1 for Phase 2.
     */
    protected final int getNumObjectiveFunctions() {
        return this.numArtificialVariables > 0 ? 2 : 1;
    }

    /**
     * Get a count of constraints corresponding to a specified relationship.
     * @param relationship relationship to count
     * @return number of constraint with the specified relationship
     */
    private int getConstraintTypeCounts(final Relationship relationship) {
        int count = 0;
        for (final LinearConstraint constraint : constraints) {
            if (constraint.getRelationship() == relationship) {
                ++count;
            }
        }
        return count;
    }

    /**
     * Get the -1 times the sum of all coefficients in the given array.
     * @param coefficients coefficients to sum
     * @return the -1 times the sum of all coefficients in the given array.
     */
    protected static double getInvertedCoefficientSum(final RealVector coefficients) {
        double sum = 0;
        for (double coefficient : coefficients.toArray()) {
            sum -= coefficient;
        }
        return sum;
    }

    /**
     * Checks whether the given column is basic.
     * @param col index of the column to check
     * @return the row that the variable is basic in.  null if the column is not basic
     */
    protected Integer getBasicRow(final int col) {
        Integer row = null;
        for (int i = 0; i < getHeight(); i++) {
            final double entry = getEntry(i, col);
            if (Precision.equals(entry, 1d, maxUlps) && (row == null)) {
                row = i;
            } else if (!Precision.equals(entry, 0d, maxUlps)) {
                return null;
            }
        }
        return row;
    }

    /**
     * Removes the phase 1 objective function, positive cost non-artificial variables,
     * and the non-basic artificial variables from this tableau.
     */
    protected void dropPhase1Objective() {
        if (getNumObjectiveFunctions() == 1) {
            return;
        }

        Set<Integer> columnsToDrop = new TreeSet<Integer>();
        columnsToDrop.add(0);

        // positive cost non-artificial variables
        for (int i = getNumObjectiveFunctions(); i < getArtificialVariableOffset(); i++) {
            final double entry = tableau.getEntry(0, i);
            if (Precision.compareTo(entry, 0d, epsilon) > 0) {
                columnsToDrop.add(i);
            }
        }

        // non-basic artificial variables
        for (int i = 0; i < getNumArtificialVariables(); i++) {
            int col = i + getArtificialVariableOffset();
            if (getBasicRow(col) == null) {
                columnsToDrop.add(col);
            }
        }

        double[][] matrix = new double[getHeight() - 1][getWidth() - columnsToDrop.size()];
        for (int i = 1; i < getHeight(); i++) {
            int col = 0;
            for (int j = 0; j < getWidth(); j++) {
                if (!columnsToDrop.contains(j)) {
                    matrix[i - 1][col++] = tableau.getEntry(i, j);
                }
            }
        }

        // remove the columns in reverse order so the indices are correct
        Integer[] drop = columnsToDrop.toArray(new Integer[columnsToDrop.size()]);
        for (int i = drop.length - 1; i >= 0; i--) {
            columnLabels.remove((int) drop[i]);
        }

        this.tableau = new Array2DRowRealMatrix(matrix);
        this.numArtificialVariables = 0;
    }

    /**
     * @param src the source array
     * @param dest the destination array
     */
    private void copyArray(final double[] src, final double[] dest) {
        System.arraycopy(src, 0, dest, getNumObjectiveFunctions(), src.length);
    }

    /**
     * Returns whether the problem is at an optimal state.
     * @return whether the model has been solved
     */
    boolean isOptimal() {
        for (int i = getNumObjectiveFunctions(); i < getWidth() - 1; i++) {
            final double entry = tableau.getEntry(0, i);
            if (Precision.compareTo(entry, 0d, epsilon) < 0) {
                return false;
            }
        }
        return true;
    }

    /**
     * Get the current solution.
     * @return current solution
     */
    protected PointValuePair getSolution() {
      int negativeVarColumn = columnLabels.indexOf(NEGATIVE_VAR_COLUMN_LABEL);
      Integer negativeVarBasicRow = negativeVarColumn > 0 ? getBasicRow(negativeVarColumn) : null;
      double mostNegative = negativeVarBasicRow == null ? 0 : getEntry(negativeVarBasicRow, getRhsOffset());

      Set<Integer> basicRows = new HashSet<Integer>();
      double[] coefficients = new double[getOriginalNumDecisionVariables()];
      for (int i = 0; i < coefficients.length; i++) {
          int colIndex = columnLabels.indexOf("x" + i);
          if (colIndex < 0) {
            coefficients[i] = 0;
            continue;
          }
          Integer basicRow = getBasicRow(colIndex);
          if (basicRow != null && basicRow == 0) {
              // if the basic row is found to be the objective function row
              // set the coefficient to 0 -> this case handles unconstrained
              // variables that are still part of the objective function
              coefficients[i] = 0;
          } else if (basicRows.contains(basicRow)) {
              // if multiple variables can take a given value
              // then we choose the first and set the rest equal to 0
              coefficients[i] = 0 - (restrictToNonNegative ? 0 : mostNegative);
          } else {
              basicRows.add(basicRow);
              coefficients[i] =
                  (basicRow == null ? 0 : getEntry(basicRow, getRhsOffset())) -
                  (restrictToNonNegative ? 0 : mostNegative);
          }
      }
      return new PointValuePair(coefficients, f.getValue(coefficients));
    }

    /**
     * Subtracts a multiple of one row from another.
     * <p>
     * After application of this operation, the following will hold:
     * <pre>minuendRow = minuendRow - multiple * subtrahendRow</pre>
     *
     * @param dividendRow index of the row
     * @param divisor value of the divisor
     */
    protected void divideRow(final int dividendRow, final double divisor) {
        for (int j = 0; j < getWidth(); j++) {
            tableau.setEntry(dividendRow, j, tableau.getEntry(dividendRow, j) / divisor);
        }
    }

    /**
     * Subtracts a multiple of one row from another.
     * <p>
     * After application of this operation, the following will hold:
     * <pre>minuendRow = minuendRow - multiple * subtrahendRow</pre>
     *
     * @param minuendRow row index
     * @param subtrahendRow row index
     * @param multiple multiplication factor
     */
    protected void subtractRow(final int minuendRow, final int subtrahendRow,
                               final double multiple) {
        for (int i = 0; i < getWidth(); i++) {
            double result = tableau.getEntry(minuendRow, i) - tableau.getEntry(subtrahendRow, i) * multiple;
            // cut-off values smaller than the CUTOFF_THRESHOLD, otherwise may lead to numerical instabilities
            if (FastMath.abs(result) < CUTOFF_THRESHOLD) {
                result = 0.0;
            }
            tableau.setEntry(minuendRow, i, result);
        }
    }

    /**
     * Get the width of the tableau.
     * @return width of the tableau
     */
    protected final int getWidth() {
        return tableau.getColumnDimension();
    }

    /**
     * Get the height of the tableau.
     * @return height of the tableau
     */
    protected final int getHeight() {
        return tableau.getRowDimension();
    }

    /**
     * Get an entry of the tableau.
     * @param row row index
     * @param column column index
     * @return entry at (row, column)
     */
    protected final double getEntry(final int row, final int column) {
        return tableau.getEntry(row, column);
    }

    /**
     * Set an entry of the tableau.
     * @param row row index
     * @param column column index
     * @param value for the entry
     */
    protected final void setEntry(final int row, final int column,
                                  final double value) {
        tableau.setEntry(row, column, value);
    }

    /**
     * Get the offset of the first slack variable.
     * @return offset of the first slack variable
     */
    protected final int getSlackVariableOffset() {
        return getNumObjectiveFunctions() + numDecisionVariables;
    }

    /**
     * Get the offset of the first artificial variable.
     * @return offset of the first artificial variable
     */
    protected final int getArtificialVariableOffset() {
        return getNumObjectiveFunctions() + numDecisionVariables + numSlackVariables;
    }

    /**
     * Get the offset of the right hand side.
     * @return offset of the right hand side
     */
    protected final int getRhsOffset() {
        return getWidth() - 1;
    }

    /**
     * Get the number of decision variables.
     * <p>
     * If variables are not restricted to positive values, this will include 1 extra decision variable to represent
     * the absolute value of the most negative variable.
     *
     * @return number of decision variables
     * @see #getOriginalNumDecisionVariables()
     */
    protected final int getNumDecisionVariables() {
        return numDecisionVariables;
    }

    /**
     * Get the original number of decision variables.
     * @return original number of decision variables
     * @see #getNumDecisionVariables()
     */
    protected final int getOriginalNumDecisionVariables() {
        return f.getCoefficients().getDimension();
    }

    /**
     * Get the number of slack variables.
     * @return number of slack variables
     */
    protected final int getNumSlackVariables() {
        return numSlackVariables;
    }

    /**
     * Get the number of artificial variables.
     * @return number of artificial variables
     */
    protected final int getNumArtificialVariables() {
        return numArtificialVariables;
    }

    /**
     * Get the tableau data.
     * @return tableau data
     */
    protected final double[][] getData() {
        return tableau.getData();
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object other) {

      if (this == other) {
        return true;
      }

      if (other instanceof SimplexTableau) {
          SimplexTableau rhs = (SimplexTableau) other;
          return (restrictToNonNegative  == rhs.restrictToNonNegative) &&
                 (numDecisionVariables   == rhs.numDecisionVariables) &&
                 (numSlackVariables      == rhs.numSlackVariables) &&
                 (numArtificialVariables == rhs.numArtificialVariables) &&
                 (epsilon                == rhs.epsilon) &&
                 (maxUlps                == rhs.maxUlps) &&
                 f.equals(rhs.f) &&
                 constraints.equals(rhs.constraints) &&
                 tableau.equals(rhs.tableau);
      }
      return false;
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return Boolean.valueOf(restrictToNonNegative).hashCode() ^
               numDecisionVariables ^
               numSlackVariables ^
               numArtificialVariables ^
               Double.valueOf(epsilon).hashCode() ^
               maxUlps ^
               f.hashCode() ^
               constraints.hashCode() ^
               tableau.hashCode();
    }

    /**
     * Serialize the instance.
     * @param oos stream where object should be written
     * @throws IOException if object cannot be written to stream
     */
    private void writeObject(ObjectOutputStream oos)
        throws IOException {
        oos.defaultWriteObject();
        MatrixUtils.serializeRealMatrix(tableau, oos);
    }

    /**
     * Deserialize the instance.
     * @param ois stream from which the object should be read
     * @throws ClassNotFoundException if a class in the stream cannot be found
     * @throws IOException if object cannot be read from the stream
     */
    private void readObject(ObjectInputStream ois)
      throws ClassNotFoundException, IOException {
        ois.defaultReadObject();
        MatrixUtils.deserializeRealMatrix(this, "tableau", ois);
    }
}
