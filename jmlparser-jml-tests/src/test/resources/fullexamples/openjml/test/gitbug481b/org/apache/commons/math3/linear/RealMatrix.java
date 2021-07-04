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

package org.apache.commons.math3.linear;

import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;

/**
 * Interface defining a real-valued matrix with basic algebraic operations.
 * <p>
 * Matrix element indexing is 0-based -- e.g., <code>getEntry(0, 0)</code>
 * returns the element in the first row, first column of the matrix.</p>
 *
 */
public interface RealMatrix extends AnyMatrix {

    /**
     * Create a new RealMatrix of the same type as the instance with the
     * supplied
     * row and column dimensions.
     *
     * @param rowDimension the number of rows in the new matrix
     * @param columnDimension the number of columns in the new matrix
     * @return a new matrix of the same type as the instance
     * @throws NotStrictlyPositiveException if row or column dimension is not
     * positive.
     * @since 2.0
     */
    RealMatrix createMatrix(int rowDimension, int columnDimension)
        throws NotStrictlyPositiveException;

    /**
     * Returns a (deep) copy of this.
     *
     * @return matrix copy
     */
    RealMatrix copy();

    /**
     * Returns the sum of {@code this} and {@code m}.
     *
     * @param m matrix to be added
     * @return {@code this + m}
     * @throws MatrixDimensionMismatchException if {@code m} is not the same
     * size as {@code this}.
     */
    RealMatrix add(RealMatrix m)
        throws MatrixDimensionMismatchException;

    /**
     * Returns {@code this} minus {@code m}.
     *
     * @param m matrix to be subtracted
     * @return {@code this - m}
     * @throws MatrixDimensionMismatchException if {@code m} is not the same
     * size as {@code this}.
     */
    RealMatrix subtract(RealMatrix m)
        throws MatrixDimensionMismatchException;

    /**
     * Returns the result of adding {@code d} to each entry of {@code this}.
     *
     * @param d value to be added to each entry
     * @return {@code d + this}
     */
    RealMatrix scalarAdd(double d);

    /**
     * Returns the result of multiplying each entry of {@code this} by
     * {@code d}.
     *
     * @param d value to multiply all entries by
     * @return {@code d * this}
     */
    RealMatrix scalarMultiply(double d);

    /**
     * Returns the result of postmultiplying {@code this} by {@code m}.
     *
     * @param m matrix to postmultiply by
     * @return {@code this * m}
     * @throws DimensionMismatchException if
     * {@code columnDimension(this) != rowDimension(m)}
     */
    RealMatrix multiply(RealMatrix m)
        throws DimensionMismatchException;

    /**
     * Returns the result of premultiplying {@code this} by {@code m}.
     *
     * @param m matrix to premultiply by
     * @return {@code m * this}
     * @throws DimensionMismatchException if
     * {@code rowDimension(this) != columnDimension(m)}
     */
    RealMatrix preMultiply(RealMatrix m)
        throws DimensionMismatchException;

    /**
     * Returns the result of multiplying {@code this} with itself {@code p}
     * times. Depending on the underlying storage, instability for high powers
     * might occur.
     *
     * @param p raise {@code this} to power {@code p}
     * @return {@code this^p}
     * @throws NotPositiveException if {@code p < 0}
     * @throws NonSquareMatrixException if the matrix is not square
     */
    RealMatrix power(final int p)
        throws NotPositiveException, NonSquareMatrixException;

    /**
     * Returns matrix entries as a two-dimensional array.
     *
     * @return 2-dimensional array of entries
     */
    double[][] getData();

    /**
     * Returns the <a href="http://mathworld.wolfram.com/MaximumAbsoluteRowSumNorm.html">
     * maximum absolute row sum norm</a> of the matrix.
     *
     * @return norm
     */
    double getNorm();

    /**
     * Returns the <a href="http://mathworld.wolfram.com/FrobeniusNorm.html">
     * Frobenius norm</a> of the matrix.
     *
     * @return norm
     */
    double getFrobeniusNorm();

    /**
     * Gets a submatrix. Rows and columns are indicated
     * counting from 0 to n-1.
     *
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @return The subMatrix containing the data of the
     * specified rows and columns.
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     */
    RealMatrix getSubMatrix(int startRow, int endRow, int startColumn,
                            int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Gets a submatrix. Rows and columns are indicated counting from 0 to n-1.
     *
     * @param selectedRows Array of row indices.
     * @param selectedColumns Array of column indices.
     * @return The subMatrix containing the data in the specified rows and
     * columns
     * @throws NullArgumentException if the row or column selections are
     * {@code null}
     * @throws NoDataException if the row or column selections are empty (zero
     * length).
     * @throws OutOfRangeException if the indices are not valid.
     */
    RealMatrix getSubMatrix(int[] selectedRows, int[] selectedColumns)
        throws NullArgumentException, NoDataException, OutOfRangeException;

    /**
     * Copy a submatrix. Rows and columns are indicated counting from 0 to n-1.
     *
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @param destination The arrays where the submatrix data should be copied
     * (if larger than rows/columns counts, only the upper-left part will be
     * used)
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @throws MatrixDimensionMismatchException if the destination array is too
     * small.
     */
    void copySubMatrix(int startRow, int endRow, int startColumn,
                       int endColumn, double[][] destination)
        throws OutOfRangeException, NumberIsTooSmallException,
        MatrixDimensionMismatchException;

    /**
     * Copy a submatrix. Rows and columns are indicated counting from 0 to n-1.
     *
     * @param selectedRows Array of row indices.
     * @param selectedColumns Array of column indices.
     * @param destination The arrays where the submatrix data should be copied
     * (if larger than rows/columns counts, only the upper-left part will be
     * used)
     * @throws NullArgumentException if the row or column selections are
     * {@code null}
     * @throws NoDataException if the row or column selections are empty (zero
     * length).
     * @throws OutOfRangeException if the indices are not valid.
     * @throws MatrixDimensionMismatchException if the destination array is too
     * small.
     */
    void copySubMatrix(int[] selectedRows, int[] selectedColumns,
                       double[][] destination)
        throws OutOfRangeException, NullArgumentException, NoDataException,
        MatrixDimensionMismatchException;

   /**
    * Replace the submatrix starting at {@code row, column} using data in the
    * input {@code subMatrix} array. Indexes are 0-based.
    * <p>
    * Example:<br>
    * Starting with <pre>
    * 1  2  3  4
    * 5  6  7  8
    * 9  0  1  2
    * </pre>
    * and <code>subMatrix = {{3, 4} {5,6}}</code>, invoking
    * {@code setSubMatrix(subMatrix,1,1))} will result in <pre>
    * 1  2  3  4
    * 5  3  4  8
    * 9  5  6  2
    * </pre></p>
    *
    * @param subMatrix  array containing the submatrix replacement data
    * @param row  row coordinate of the top, left element to be replaced
    * @param column  column coordinate of the top, left element to be replaced
    * @throws NoDataException if {@code subMatrix} is empty.
    * @throws OutOfRangeException if {@code subMatrix} does not fit into
    * this matrix from element in {@code (row, column)}.
    * @throws DimensionMismatchException if {@code subMatrix} is not rectangular
    * (not all rows have the same length) or empty.
    * @throws NullArgumentException if {@code subMatrix} is {@code null}.
    * @since 2.0
    */
    void setSubMatrix(double[][] subMatrix, int row, int column)
        throws NoDataException, OutOfRangeException,
        DimensionMismatchException, NullArgumentException;

   /**
    * Get the entries at the given row index as a row matrix.  Row indices start
    * at 0.
    *
    * @param row Row to be fetched.
    * @return row Matrix.
    * @throws OutOfRangeException if the specified row index is invalid.
    */
   RealMatrix getRowMatrix(int row) throws OutOfRangeException;

    /**
     * Sets the specified {@code row} of {@code this} matrix to the entries of
     * the specified row {@code matrix}. Row indices start at 0.
     *
     * @param row Row to be set.
     * @param matrix Row matrix to be copied (must have one row and the same
     * number of columns as the instance).
     * @throws OutOfRangeException if the specified row index is invalid.
     * @throws MatrixDimensionMismatchException if the row dimension of the
     * {@code matrix} is not {@code 1}, or the column dimensions of {@code this}
     * and {@code matrix} do not match.
     */
    void setRowMatrix(int row, RealMatrix matrix)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Get the entries at the given column index as a column matrix. Column
     * indices start at 0.
     *
     * @param column Column to be fetched.
     * @return column Matrix.
     * @throws OutOfRangeException if the specified column index is invalid.
     */
    RealMatrix getColumnMatrix(int column)
        throws OutOfRangeException;

    /**
     * Sets the specified {@code column} of {@code this} matrix to the entries
     * of the specified column {@code matrix}. Column indices start at 0.
     *
     * @param column Column to be set.
     * @param matrix Column matrix to be copied (must have one column and the
     * same number of rows as the instance).
     * @throws OutOfRangeException if the specified column index is invalid.
     * @throws MatrixDimensionMismatchException if the column dimension of the
     * {@code matrix} is not {@code 1}, or the row dimensions of {@code this}
     * and {@code matrix} do not match.
     */
    void setColumnMatrix(int column, RealMatrix matrix)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Returns the entries in row number {@code row} as a vector. Row indices
     * start at 0.
     *
     * @param row Row to be fetched.
     * @return a row vector.
     * @throws OutOfRangeException if the specified row index is invalid.
     */
    RealVector getRowVector(int row)
        throws OutOfRangeException;

    /**
     * Sets the specified {@code row} of {@code this} matrix to the entries of
     * the specified {@code vector}. Row indices start at 0.
     *
     * @param row Row to be set.
     * @param vector row vector to be copied (must have the same number of
     * column as the instance).
     * @throws OutOfRangeException if the specified row index is invalid.
     * @throws MatrixDimensionMismatchException if the {@code vector} dimension
     * does not match the column dimension of {@code this} matrix.
     */
    void setRowVector(int row, RealVector vector)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Get the entries at the given column index as a vector. Column indices
     * start at 0.
     *
     * @param column Column to be fetched.
     * @return a column vector.
     * @throws OutOfRangeException if the specified column index is invalid
     */
    RealVector getColumnVector(int column)
        throws OutOfRangeException;

    /**
     * Sets the specified {@code column} of {@code this} matrix to the entries
     * of the specified {@code vector}. Column indices start at 0.
     *
     * @param column Column to be set.
     * @param vector column vector to be copied (must have the same number of
     * rows as the instance).
     * @throws OutOfRangeException if the specified column index is invalid.
     * @throws MatrixDimensionMismatchException if the {@code vector} dimension
     * does not match the row dimension of {@code this} matrix.
     */
    void setColumnVector(int column, RealVector vector)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Get the entries at the given row index. Row indices start at 0.
     *
     * @param row Row to be fetched.
     * @return the array of entries in the row.
     * @throws OutOfRangeException if the specified row index is not valid.
     */
    double[] getRow(int row) throws OutOfRangeException;

    /**
     * Sets the specified {@code row} of {@code this} matrix to the entries
     * of the specified {@code array}. Row indices start at 0.
     *
     * @param row Row to be set.
     * @param array Row matrix to be copied (must have the same number of
     * columns as the instance)
     * @throws OutOfRangeException if the specified row index is invalid.
     * @throws MatrixDimensionMismatchException if the {@code array} length does
     * not match the column dimension of {@code this} matrix.
     */
    void setRow(int row, double[] array)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Get the entries at the given column index as an array. Column indices
     * start at 0.
     *
     * @param column Column to be fetched.
     * @return the array of entries in the column.
     * @throws OutOfRangeException if the specified column index is not valid.
     */
    double[] getColumn(int column) throws OutOfRangeException;

    /**
     * Sets the specified {@code column} of {@code this} matrix to the entries
     * of the specified {@code array}. Column indices start at 0.
     *
     * @param column Column to be set.
     * @param array Column array to be copied (must have the same number of
     * rows as the instance).
     * @throws OutOfRangeException if the specified column index is invalid.
     * @throws MatrixDimensionMismatchException if the {@code array} length does
     * not match the row dimension of {@code this} matrix.
     */
    void setColumn(int column, double[] array)
        throws OutOfRangeException, MatrixDimensionMismatchException;

    /**
     * Get the entry in the specified row and column. Row and column indices
     * start at 0.
     *
     * @param row Row index of entry to be fetched.
     * @param column Column index of entry to be fetched.
     * @return the matrix entry at {@code (row, column)}.
     * @throws OutOfRangeException if the row or column index is not valid.
     */
    double getEntry(int row, int column) throws OutOfRangeException;

    /**
     * Set the entry in the specified row and column. Row and column indices
     * start at 0.
     *
     * @param row Row index of entry to be set.
     * @param column Column index of entry to be set.
     * @param value the new value of the entry.
     * @throws OutOfRangeException if the row or column index is not valid
     * @since 2.0
     */
    void setEntry(int row, int column, double value) throws OutOfRangeException;

    /**
     * Adds (in place) the specified value to the specified entry of
     * {@code this} matrix. Row and column indices start at 0.
     *
     * @param row Row index of the entry to be modified.
     * @param column Column index of the entry to be modified.
     * @param increment value to add to the matrix entry.
     * @throws OutOfRangeException if the row or column index is not valid.
     * @since 2.0
     */
    void addToEntry(int row, int column, double increment) throws OutOfRangeException;

    /**
     * Multiplies (in place) the specified entry of {@code this} matrix by the
     * specified value. Row and column indices start at 0.
     *
     * @param row Row index of the entry to be modified.
     * @param column Column index of the entry to be modified.
     * @param factor Multiplication factor for the matrix entry.
     * @throws OutOfRangeException if the row or column index is not valid.
     * @since 2.0
     */
    void multiplyEntry(int row, int column, double factor) throws OutOfRangeException;

    /**
     * Returns the transpose of this matrix.
     *
     * @return transpose matrix
     */
    RealMatrix transpose();

    /**
     * Returns the <a href="http://mathworld.wolfram.com/MatrixTrace.html">
     * trace</a> of the matrix (the sum of the elements on the main diagonal).
     *
     * @return the trace.
     * @throws NonSquareMatrixException if the matrix is not square.
     */
    double getTrace() throws NonSquareMatrixException;

    /**
     * Returns the result of multiplying this by the vector {@code v}.
     *
     * @param v the vector to operate on
     * @return {@code this * v}
     * @throws DimensionMismatchException if the length of {@code v} does not
     * match the column dimension of {@code this}.
     */
    double[] operate(double[] v) throws DimensionMismatchException;

    /**
     * Returns the result of multiplying this by the vector {@code v}.
     *
     * @param v the vector to operate on
     * @return {@code this * v}
     * @throws DimensionMismatchException if the dimension of {@code v} does not
     * match the column dimension of {@code this}.
     */
    RealVector operate(RealVector v) throws DimensionMismatchException;

    /**
     * Returns the (row) vector result of premultiplying this by the vector {@code v}.
     *
     * @param v the row vector to premultiply by
     * @return {@code v * this}
     * @throws DimensionMismatchException if the length of {@code v} does not
     * match the row dimension of {@code this}.
     */
    double[] preMultiply(double[] v) throws DimensionMismatchException;

    /**
     * Returns the (row) vector result of premultiplying this by the vector {@code v}.
     *
     * @param v the row vector to premultiply by
     * @return {@code v * this}
     * @throws DimensionMismatchException if the dimension of {@code v} does not
     * match the row dimension of {@code this}.
     */
    RealVector preMultiply(RealVector v) throws DimensionMismatchException;

    /**
     * Visit (and possibly change) all matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInRowOrder(RealMatrixChangingVisitor visitor);

    /**
     * Visit (but don't change) all matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInRowOrder(RealMatrixPreservingVisitor visitor);

    /**
     * Visit (and possibly change) some matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInRowOrder(RealMatrixChangingVisitor visitor, int startRow,
        int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (but don't change) some matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInRowOrder(RealMatrixPreservingVisitor visitor, int startRow,
        int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (and possibly change) all matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInColumnOrder(RealMatrixChangingVisitor visitor);

    /**
     * Visit (but don't change) all matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInColumnOrder(RealMatrixPreservingVisitor visitor);

    /**
     * Visit (and possibly change) some matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInColumnOrder(RealMatrixChangingVisitor visitor, int startRow,
        int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (but don't change) some matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInColumnOrder(RealMatrixPreservingVisitor visitor, int startRow,
        int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (and possibly change) all matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInOptimizedOrder(RealMatrixChangingVisitor visitor);

    /**
     * Visit (but don't change) all matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInOptimizedOrder(RealMatrixPreservingVisitor visitor);

    /**
     * Visit (and possibly change) some matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    double walkInOptimizedOrder(RealMatrixChangingVisitor visitor,
        int startRow, int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (but don't change) some matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @throws OutOfRangeException if the indices are not valid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @see #walkInRowOrder(RealMatrixChangingVisitor)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor)
     * @see #walkInRowOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor)
     * @see #walkInColumnOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(RealMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(RealMatrixChangingVisitor, int, int, int, int)
     * @return the value returned by {@link RealMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    double walkInOptimizedOrder(RealMatrixPreservingVisitor visitor,
        int startRow, int endRow, int startColumn, int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException;
}
