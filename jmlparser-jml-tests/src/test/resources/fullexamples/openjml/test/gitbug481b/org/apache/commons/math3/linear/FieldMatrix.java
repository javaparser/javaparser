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


import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;

/**
 * Interface defining field-valued matrix with basic algebraic operations.
 * <p>
 * Matrix element indexing is 0-based -- e.g., <code>getEntry(0, 0)</code>
 * returns the element in the first row, first column of the matrix.</p>
 *
 * @param <T> the type of the field elements
 */
public interface FieldMatrix<T extends FieldElement<T>> extends AnyMatrix {
    /**
     * Get the type of field elements of the matrix.
     *
     * @return the type of field elements of the matrix.
     */
    Field<T> getField();

    /**
     * Create a new FieldMatrix<T> of the same type as the instance with
     * the supplied row and column dimensions.
     *
     * @param rowDimension  the number of rows in the new matrix
     * @param columnDimension  the number of columns in the new matrix
     * @return a new matrix of the same type as the instance
     * @throws NotStrictlyPositiveException if row or column dimension is not
     * positive.
     * @since 2.0
     */
    FieldMatrix<T> createMatrix(final int rowDimension, final int columnDimension)
    throws NotStrictlyPositiveException;

    /**
     * Make a (deep) copy of this.
     *
     * @return a copy of this matrix.
     */
    FieldMatrix<T> copy();

    /**
     * Compute the sum of this and m.
     *
     * @param m Matrix to be added.
     * @return {@code this} + {@code m}.
     * @throws MatrixDimensionMismatchException if {@code m} is not the same
     * size as {@code this} matrix.
     */
    FieldMatrix<T> add(FieldMatrix<T> m) throws MatrixDimensionMismatchException;

    /**
     * Subtract {@code m} from this matrix.
     *
     * @param m Matrix to be subtracted.
     * @return {@code this} - {@code m}.
     * @throws MatrixDimensionMismatchException if {@code m} is not the same
     * size as {@code this} matrix.
     */
    FieldMatrix<T> subtract(FieldMatrix<T> m) throws MatrixDimensionMismatchException;

     /**
     * Increment each entry of this matrix.
     *
     * @param d Value to be added to each entry.
     * @return {@code d} + {@code this}.
     */
    FieldMatrix<T> scalarAdd(T d);

    /**
     * Multiply each entry by {@code d}.
     *
     * @param d Value to multiply all entries by.
     * @return {@code d} * {@code this}.
     */
    FieldMatrix<T> scalarMultiply(T d);

    /**
     * Postmultiply this matrix by {@code m}.
     *
     * @param m  Matrix to postmultiply by.
     * @return {@code this} * {@code m}.
     * @throws DimensionMismatchException if the number of columns of
     * {@code this} matrix is not equal to the number of rows of matrix
     * {@code m}.
     */
    FieldMatrix<T> multiply(FieldMatrix<T> m) throws DimensionMismatchException;

    /**
     * Premultiply this matrix by {@code m}.
     *
     * @param m Matrix to premultiply by.
     * @return {@code m} * {@code this}.
     * @throws DimensionMismatchException if the number of columns of {@code m}
     * differs from the number of rows of {@code this} matrix.
     */
    FieldMatrix<T> preMultiply(FieldMatrix<T> m) throws DimensionMismatchException;

    /**
     * Returns the result multiplying this with itself <code>p</code> times.
     * Depending on the type of the field elements, T, instability for high
     * powers might occur.
     *
     * @param p raise this to power p
     * @return this^p
     * @throws NotPositiveException if {@code p < 0}
     * @throws NonSquareMatrixException if {@code this matrix} is not square
     */
    FieldMatrix<T> power(final int p) throws NonSquareMatrixException,
    NotPositiveException;

    /**
     * Returns matrix entries as a two-dimensional array.
     *
     * @return a 2-dimensional array of entries.
     */
    T[][] getData();

    /**
     * Get a submatrix. Rows and columns are indicated
     * counting from 0 to n - 1.
     *
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @return the matrix containing the data of the specified rows and columns.
     * @throws NumberIsTooSmallException is {@code endRow < startRow} of
     * {@code endColumn < startColumn}.
     * @throws OutOfRangeException if the indices are not valid.
     */
   FieldMatrix<T> getSubMatrix(int startRow, int endRow, int startColumn, int endColumn)
   throws NumberIsTooSmallException, OutOfRangeException;

   /**
    * Get a submatrix. Rows and columns are indicated
    * counting from 0 to n - 1.
    *
    * @param selectedRows Array of row indices.
    * @param selectedColumns Array of column indices.
    * @return the matrix containing the data in the
    * specified rows and columns.
    * @throws NoDataException if {@code selectedRows} or
    * {@code selectedColumns} is empty
    * @throws NullArgumentException if {@code selectedRows} or
    * {@code selectedColumns} is {@code null}.
    * @throws OutOfRangeException if row or column selections are not valid.
    */
   FieldMatrix<T> getSubMatrix(int[] selectedRows, int[] selectedColumns)
   throws NoDataException, NullArgumentException, OutOfRangeException;

   /**
    * Copy a submatrix. Rows and columns are 0-based. The designated submatrix
    * is copied into the top left portion of the destination array.
    *
    * @param startRow Initial row index.
    * @param endRow Final row index (inclusive).
    * @param startColumn Initial column index.
    * @param endColumn Final column index (inclusive).
    * @param destination The array where the submatrix data should be copied
    * (if larger than rows/columns counts, only the upper-left part will be modified).
    * @throws MatrixDimensionMismatchException if the dimensions of
    * {@code destination} are not large enough to hold the submatrix.
    * @throws NumberIsTooSmallException if {@code endRow < startRow} or
    * {@code endColumn < startColumn}.
    * @throws OutOfRangeException if the indices are not valid.
    */
    void copySubMatrix(int startRow, int endRow, int startColumn, int endColumn,
                       T[][] destination)
    throws MatrixDimensionMismatchException, NumberIsTooSmallException,
    OutOfRangeException;

  /**
   * Copy a submatrix. Rows and columns are indicated
   * counting from 0 to n - 1.
   *
   * @param selectedRows Array of row indices.
   * @param selectedColumns Array of column indices.
   * @param destination Arrays where the submatrix data should be copied
   * (if larger than rows/columns counts, only the upper-left part will be used)
   * @throws MatrixDimensionMismatchException if the dimensions of
   * {@code destination} do not match those of {@code this}.
   * @throws NoDataException if {@code selectedRows} or
   * {@code selectedColumns} is empty
   * @throws NullArgumentException if {@code selectedRows} or
   * {@code selectedColumns} is {@code null}.
   * @throws OutOfRangeException if the indices are not valid.
   */
  void copySubMatrix(int[] selectedRows, int[] selectedColumns, T[][] destination)
  throws MatrixDimensionMismatchException, NoDataException, NullArgumentException,
  OutOfRangeException;

    /**
     * Replace the submatrix starting at {@code (row, column)} using data in the
     * input {@code subMatrix} array. Indexes are 0-based.
     * <p>
     * Example:<br>
     * Starting with
     *
     * <pre>
     * 1  2  3  4
     * 5  6  7  8
     * 9  0  1  2
     * </pre>
     *
     * and <code>subMatrix = {{3, 4} {5,6}}</code>, invoking
     * <code>setSubMatrix(subMatrix,1,1))</code> will result in
     *
     * <pre>
     * 1  2  3  4
     * 5  3  4  8
     * 9  5  6  2
     * </pre>
     *
     * </p>
     *
     * @param subMatrix Array containing the submatrix replacement data.
     * @param row Row coordinate of the top-left element to be replaced.
     * @param column Column coordinate of the top-left element to be replaced.
     * @throws OutOfRangeException if {@code subMatrix} does not fit into this
     * matrix from element in {@code (row, column)}.
     * @throws NoDataException if a row or column of {@code subMatrix} is empty.
     * @throws DimensionMismatchException if {@code subMatrix} is not
     * rectangular (not all rows have the same length).
     * @throws NullArgumentException if {@code subMatrix} is {@code null}.
     * @since 2.0
     */
    void setSubMatrix(T[][] subMatrix, int row, int column)
        throws DimensionMismatchException, OutOfRangeException,
        NoDataException, NullArgumentException;

   /**
    * Get the entries in row number {@code row}
    * as a row matrix.
    *
    * @param row Row to be fetched.
    * @return a row matrix.
    * @throws OutOfRangeException if the specified row index is invalid.
    */
   FieldMatrix<T> getRowMatrix(int row) throws OutOfRangeException;

   /**
    * Set the entries in row number {@code row}
    * as a row matrix.
    *
    * @param row Row to be set.
    * @param matrix Row matrix (must have one row and the same number
    * of columns as the instance).
    * @throws OutOfRangeException if the specified row index is invalid.
    * @throws MatrixDimensionMismatchException
    * if the matrix dimensions do not match one instance row.
    */
   void setRowMatrix(int row, FieldMatrix<T> matrix)
   throws MatrixDimensionMismatchException, OutOfRangeException;

   /**
    * Get the entries in column number {@code column}
    * as a column matrix.
    *
    * @param column Column to be fetched.
    * @return a column matrix.
    * @throws OutOfRangeException if the specified column index is invalid.
    */
   FieldMatrix<T> getColumnMatrix(int column) throws OutOfRangeException;

   /**
    * Set the entries in column number {@code column}
    * as a column matrix.
    *
    * @param column Column to be set.
    * @param matrix column matrix (must have one column and the same
    * number of rows as the instance).
    * @throws OutOfRangeException if the specified column index is invalid.
    * @throws MatrixDimensionMismatchException if the matrix dimensions do
    * not match one instance column.
    */
   void setColumnMatrix(int column, FieldMatrix<T> matrix)
   throws MatrixDimensionMismatchException, OutOfRangeException;

   /**
    * Get the entries in row number {@code row}
    * as a vector.
    *
    * @param row Row to be fetched
    * @return a row vector.
    * @throws OutOfRangeException if the specified row index is invalid.
    */
   FieldVector<T> getRowVector(int row) throws OutOfRangeException;

   /**
    * Set the entries in row number {@code row}
    * as a vector.
    *
    * @param row Row to be set.
    * @param vector row vector (must have the same number of columns
    * as the instance).
    * @throws OutOfRangeException if the specified row index is invalid.
    * @throws MatrixDimensionMismatchException if the vector dimension does not
    * match one instance row.
    */
   void setRowVector(int row, FieldVector<T> vector)
   throws MatrixDimensionMismatchException, OutOfRangeException;

   /**
    * Returns the entries in column number {@code column}
    * as a vector.
    *
    * @param column Column to be fetched.
    * @return a column vector.
    * @throws OutOfRangeException if the specified column index is invalid.
    */
   FieldVector<T> getColumnVector(int column) throws OutOfRangeException;

   /**
    * Set the entries in column number {@code column}
    * as a vector.
    *
    * @param column Column to be set.
    * @param vector Column vector (must have the same number of rows
    * as the instance).
    * @throws OutOfRangeException if the specified column index is invalid.
    * @throws MatrixDimensionMismatchException if the vector dimension does not
    * match one instance column.
    */
   void setColumnVector(int column, FieldVector<T> vector)
   throws MatrixDimensionMismatchException, OutOfRangeException;

    /**
     * Get the entries in row number {@code row} as an array.
     *
     * @param row Row to be fetched.
     * @return array of entries in the row.
     * @throws OutOfRangeException if the specified row index is not valid.
     */
    T[] getRow(int row) throws OutOfRangeException;

    /**
     * Set the entries in row number {@code row}
     * as a row matrix.
     *
     * @param row Row to be set.
     * @param array Row matrix (must have the same number of columns as
     * the instance).
     * @throws OutOfRangeException if the specified row index is invalid.
     * @throws MatrixDimensionMismatchException if the array size does not match
     * one instance row.
     */
    void setRow(int row, T[] array) throws MatrixDimensionMismatchException,
    OutOfRangeException;

    /**
     * Get the entries in column number {@code col} as an array.
     *
     * @param column the column to be fetched
     * @return array of entries in the column
     * @throws OutOfRangeException if the specified column index is not valid.
     */
    T[] getColumn(int column) throws OutOfRangeException;

    /**
     * Set the entries in column number {@code column}
     * as a column matrix.
     *
     * @param column the column to be set
     * @param array column array (must have the same number of rows as the instance)
     * @throws OutOfRangeException if the specified column index is invalid.
     * @throws MatrixDimensionMismatchException if the array size does not match
     * one instance column.
     */
    void setColumn(int column, T[] array) throws MatrixDimensionMismatchException,
    OutOfRangeException;

    /**
     * Returns the entry in the specified row and column.
     *
     * @param row  row location of entry to be fetched
     * @param column  column location of entry to be fetched
     * @return matrix entry in row,column
     * @throws OutOfRangeException if the row or column index is not valid.
     */
    T getEntry(int row, int column) throws OutOfRangeException;

    /**
     * Set the entry in the specified row and column.
     *
     * @param row  row location of entry to be set
     * @param column  column location of entry to be set
     * @param value matrix entry to be set in row,column
     * @throws OutOfRangeException if the row or column index is not valid.
     * @since 2.0
     */
    void setEntry(int row, int column, T value) throws OutOfRangeException;

    /**
     * Change an entry in the specified row and column.
     *
     * @param row Row location of entry to be set.
     * @param column Column location of entry to be set.
     * @param increment Value to add to the current matrix entry in
     * {@code (row, column)}.
     * @throws OutOfRangeException if the row or column index is not valid.
     * @since 2.0
     */
    void addToEntry(int row, int column, T increment) throws OutOfRangeException;

    /**
     * Change an entry in the specified row and column.
     *
     * @param row Row location of entry to be set.
     * @param column Column location of entry to be set.
     * @param factor Multiplication factor for the current matrix entry
     * in {@code (row,column)}
     * @throws OutOfRangeException if the row or column index is not valid.
     * @since 2.0
     */
    void multiplyEntry(int row, int column, T factor) throws OutOfRangeException;

    /**
     * Returns the transpose of this matrix.
     *
     * @return transpose matrix
     */
    FieldMatrix<T> transpose();

    /**
     * Returns the <a href="http://mathworld.wolfram.com/MatrixTrace.html">
     * trace</a> of the matrix (the sum of the elements on the main diagonal).
     *
     * @return trace
     * @throws NonSquareMatrixException if the matrix is not square.
     */
    T getTrace() throws NonSquareMatrixException;

    /**
     * Returns the result of multiplying this by the vector {@code v}.
     *
     * @param v the vector to operate on
     * @return {@code this * v}
     * @throws DimensionMismatchException if the number of columns of
     * {@code this} matrix is not equal to the size of the vector {@code v}.
     */
    T[] operate(T[] v) throws DimensionMismatchException;

    /**
     * Returns the result of multiplying this by the vector {@code v}.
     *
     * @param v the vector to operate on
     * @return {@code this * v}
     * @throws DimensionMismatchException if the number of columns of
     * {@code this} matrix is not equal to the size of the vector {@code v}.
     */
    FieldVector<T> operate(FieldVector<T> v) throws DimensionMismatchException;

    /**
     * Returns the (row) vector result of premultiplying this by the vector
     * {@code v}.
     *
     * @param v the row vector to premultiply by
     * @return {@code v * this}
     * @throws DimensionMismatchException if the number of rows of {@code this}
     * matrix is not equal to the size of the vector {@code v}
     */
    T[] preMultiply(T[] v) throws DimensionMismatchException;

    /**
     * Returns the (row) vector result of premultiplying this by the vector
     * {@code v}.
     *
     * @param v the row vector to premultiply by
     * @return {@code v * this}
     * @throws DimensionMismatchException if the number of rows of {@code this}
     * matrix is not equal to the size of the vector {@code v}
     */
    FieldVector<T> preMultiply(FieldVector<T> v) throws DimensionMismatchException;

    /**
     * Visit (and possibly change) all matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInRowOrder(FieldMatrixChangingVisitor<T> visitor);

    /**
     * Visit (but don't change) all matrix entries in row order.
     * <p>Row order starts at upper left and iterating through all elements
     * of a row from left to right before going to the leftmost element
     * of the next row.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInRowOrder(FieldMatrixPreservingVisitor<T> visitor);

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
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInRowOrder(FieldMatrixChangingVisitor<T> visitor,
                     int startRow, int endRow, int startColumn, int endColumn)
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
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInRowOrder(FieldMatrixPreservingVisitor<T> visitor,
                     int startRow, int endRow, int startColumn, int endColumn)
    throws OutOfRangeException, NumberIsTooSmallException;

    /**
     * Visit (and possibly change) all matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInColumnOrder(FieldMatrixChangingVisitor<T> visitor);

    /**
     * Visit (but don't change) all matrix entries in column order.
     * <p>Column order starts at upper left and iterating through all elements
     * of a column from top to bottom before going to the topmost element
     * of the next column.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInColumnOrder(FieldMatrixPreservingVisitor<T> visitor);

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
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @throws OutOfRangeException if the indices are not valid.
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInColumnOrder(FieldMatrixChangingVisitor<T> visitor,
                        int startRow, int endRow, int startColumn, int endColumn)
    throws NumberIsTooSmallException, OutOfRangeException;

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
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @throws OutOfRangeException if the indices are not valid.
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInColumnOrder(FieldMatrixPreservingVisitor<T> visitor,
                        int startRow, int endRow, int startColumn, int endColumn)
    throws NumberIsTooSmallException, OutOfRangeException;

    /**
     * Visit (and possibly change) all matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInOptimizedOrder(FieldMatrixChangingVisitor<T> visitor);

    /**
     * Visit (but don't change) all matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInOptimizedOrder(FieldMatrixPreservingVisitor<T> visitor);

    /**
     * Visit (and possibly change) some matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @throws OutOfRangeException if the indices are not valid.
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixChangingVisitor#end()} at the end
     * of the walk
     */
    T walkInOptimizedOrder(FieldMatrixChangingVisitor<T> visitor,
                           int startRow, int endRow, int startColumn, int endColumn)
    throws NumberIsTooSmallException, OutOfRangeException;

    /**
     * Visit (but don't change) some matrix entries using the fastest possible order.
     * <p>The fastest walking order depends on the exact matrix class. It may be
     * different from traditional row or column orders.</p>
     * @param visitor visitor used to process all matrix entries
     * @param startRow Initial row index
     * @param endRow Final row index (inclusive)
     * @param startColumn Initial column index
     * @param endColumn Final column index (inclusive)
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     * @throws OutOfRangeException if the indices are not valid.
     * @see #walkInRowOrder(FieldMatrixChangingVisitor)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor)
     * @see #walkInRowOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInRowOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor)
     * @see #walkInColumnOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @see #walkInColumnOrder(FieldMatrixPreservingVisitor, int, int, int, int)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixPreservingVisitor)
     * @see #walkInOptimizedOrder(FieldMatrixChangingVisitor, int, int, int, int)
     * @return the value returned by {@link FieldMatrixPreservingVisitor#end()} at the end
     * of the walk
     */
    T walkInOptimizedOrder(FieldMatrixPreservingVisitor<T> visitor,
                           int startRow, int endRow, int startColumn, int endColumn)
    throws NumberIsTooSmallException, OutOfRangeException;
}
