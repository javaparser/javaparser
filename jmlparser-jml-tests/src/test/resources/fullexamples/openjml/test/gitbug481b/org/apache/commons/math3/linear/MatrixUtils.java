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

import java.io.IOException;
import java.io.ObjectInputStream;
import java.io.ObjectOutputStream;
import java.util.Arrays;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.ZeroException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.fraction.BigFraction;
import org.apache.commons.math3.fraction.Fraction;
import org.apache.commons.math3.util.FastMath;
import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.util.MathUtils;
import org.apache.commons.math3.util.Precision;

/**
 * A collection of static methods that operate on or return matrices.
 *
 */
public class MatrixUtils {

    /**
     * The default format for {@link RealMatrix} objects.
     * @since 3.1
     */
    public static final RealMatrixFormat DEFAULT_FORMAT = RealMatrixFormat.getInstance();

    /**
     * A format for {@link RealMatrix} objects compatible with octave.
     * @since 3.1
     */
    public static final RealMatrixFormat OCTAVE_FORMAT = new RealMatrixFormat("[", "]", "", "", "; ", ", ");

    /**
     * Private constructor.
     */
    private MatrixUtils() {
        super();
    }

    /**
     * Returns a {@link RealMatrix} with specified dimensions.
     * <p>The type of matrix returned depends on the dimension. Below
     * 2<sup>12</sup> elements (i.e. 4096 elements or 64&times;64 for a
     * square matrix) which can be stored in a 32kB array, a {@link
     * Array2DRowRealMatrix} instance is built. Above this threshold a {@link
     * BlockRealMatrix} instance is built.</p>
     * <p>The matrix elements are all set to 0.0.</p>
     * @param rows number of rows of the matrix
     * @param columns number of columns of the matrix
     * @return  RealMatrix with specified dimensions
     * @see #createRealMatrix(double[][])
     */
    public static RealMatrix createRealMatrix(final int rows, final int columns) {
        return (rows * columns <= 4096) ?
                new Array2DRowRealMatrix(rows, columns) : new BlockRealMatrix(rows, columns);
    }

    /**
     * Returns a {@link FieldMatrix} with specified dimensions.
     * <p>The type of matrix returned depends on the dimension. Below
     * 2<sup>12</sup> elements (i.e. 4096 elements or 64&times;64 for a
     * square matrix), a {@link FieldMatrix} instance is built. Above
     * this threshold a {@link BlockFieldMatrix} instance is built.</p>
     * <p>The matrix elements are all set to field.getZero().</p>
     * @param <T> the type of the field elements
     * @param field field to which the matrix elements belong
     * @param rows number of rows of the matrix
     * @param columns number of columns of the matrix
     * @return  FieldMatrix with specified dimensions
     * @see #createFieldMatrix(FieldElement[][])
     * @since 2.0
     */
    public static <T extends FieldElement<T>> FieldMatrix<T> createFieldMatrix(final Field<T> field,
                                                                               final int rows,
                                                                               final int columns) {
        return (rows * columns <= 4096) ?
                new Array2DRowFieldMatrix<T>(field, rows, columns) : new BlockFieldMatrix<T>(field, rows, columns);
    }

    /**
     * Returns a {@link RealMatrix} whose entries are the the values in the
     * the input array.
     * <p>The type of matrix returned depends on the dimension. Below
     * 2<sup>12</sup> elements (i.e. 4096 elements or 64&times;64 for a
     * square matrix) which can be stored in a 32kB array, a {@link
     * Array2DRowRealMatrix} instance is built. Above this threshold a {@link
     * BlockRealMatrix} instance is built.</p>
     * <p>The input array is copied, not referenced.</p>
     *
     * @param data input array
     * @return  RealMatrix containing the values of the array
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if {@code data} is not rectangular (not all rows have the same length).
     * @throws NoDataException if a row or column is empty.
     * @throws NullArgumentException if either {@code data} or {@code data[0]}
     * is {@code null}.
     * @throws DimensionMismatchException if {@code data} is not rectangular.
     * @see #createRealMatrix(int, int)
     */
    public static RealMatrix createRealMatrix(double[][] data)
        throws NullArgumentException, DimensionMismatchException,
        NoDataException {
        if (data == null ||
            data[0] == null) {
            throw new NullArgumentException();
        }
        return (data.length * data[0].length <= 4096) ?
                new Array2DRowRealMatrix(data) : new BlockRealMatrix(data);
    }

    /**
     * Returns a {@link FieldMatrix} whose entries are the the values in the
     * the input array.
     * <p>The type of matrix returned depends on the dimension. Below
     * 2<sup>12</sup> elements (i.e. 4096 elements or 64&times;64 for a
     * square matrix), a {@link FieldMatrix} instance is built. Above
     * this threshold a {@link BlockFieldMatrix} instance is built.</p>
     * <p>The input array is copied, not referenced.</p>
     * @param <T> the type of the field elements
     * @param data input array
     * @return a matrix containing the values of the array.
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if {@code data} is not rectangular (not all rows have the same length).
     * @throws NoDataException if a row or column is empty.
     * @throws NullArgumentException if either {@code data} or {@code data[0]}
     * is {@code null}.
     * @see #createFieldMatrix(Field, int, int)
     * @since 2.0
     */
    public static <T extends FieldElement<T>> FieldMatrix<T> createFieldMatrix(T[][] data)
        throws DimensionMismatchException, NoDataException, NullArgumentException {
        if (data == null ||
            data[0] == null) {
            throw new NullArgumentException();
        }
        return (data.length * data[0].length <= 4096) ?
                new Array2DRowFieldMatrix<T>(data) : new BlockFieldMatrix<T>(data);
    }

    /**
     * Returns <code>dimension x dimension</code> identity matrix.
     *
     * @param dimension dimension of identity matrix to generate
     * @return identity matrix
     * @throws IllegalArgumentException if dimension is not positive
     * @since 1.1
     */
    public static RealMatrix createRealIdentityMatrix(int dimension) {
        final RealMatrix m = createRealMatrix(dimension, dimension);
        for (int i = 0; i < dimension; ++i) {
            m.setEntry(i, i, 1.0);
        }
        return m;
    }

    /**
     * Returns <code>dimension x dimension</code> identity matrix.
     *
     * @param <T> the type of the field elements
     * @param field field to which the elements belong
     * @param dimension dimension of identity matrix to generate
     * @return identity matrix
     * @throws IllegalArgumentException if dimension is not positive
     * @since 2.0
     */
    public static <T extends FieldElement<T>> FieldMatrix<T>
        createFieldIdentityMatrix(final Field<T> field, final int dimension) {
        final T zero = field.getZero();
        final T one  = field.getOne();
        final T[][] d = MathArrays.buildArray(field, dimension, dimension);
        for (int row = 0; row < dimension; row++) {
            final T[] dRow = d[row];
            Arrays.fill(dRow, zero);
            dRow[row] = one;
        }
        return new Array2DRowFieldMatrix<T>(field, d, false);
    }

    /**
     * Returns a diagonal matrix with specified elements.
     *
     * @param diagonal diagonal elements of the matrix (the array elements
     * will be copied)
     * @return diagonal matrix
     * @since 2.0
     */
    public static RealMatrix createRealDiagonalMatrix(final double[] diagonal) {
        final RealMatrix m = createRealMatrix(diagonal.length, diagonal.length);
        for (int i = 0; i < diagonal.length; ++i) {
            m.setEntry(i, i, diagonal[i]);
        }
        return m;
    }

    /**
     * Returns a diagonal matrix with specified elements.
     *
     * @param <T> the type of the field elements
     * @param diagonal diagonal elements of the matrix (the array elements
     * will be copied)
     * @return diagonal matrix
     * @since 2.0
     */
    public static <T extends FieldElement<T>> FieldMatrix<T>
        createFieldDiagonalMatrix(final T[] diagonal) {
        final FieldMatrix<T> m =
            createFieldMatrix(diagonal[0].getField(), diagonal.length, diagonal.length);
        for (int i = 0; i < diagonal.length; ++i) {
            m.setEntry(i, i, diagonal[i]);
        }
        return m;
    }

    /**
     * Creates a {@link RealVector} using the data from the input array.
     *
     * @param data the input data
     * @return a data.length RealVector
     * @throws NoDataException if {@code data} is empty.
     * @throws NullArgumentException if {@code data} is {@code null}.
     */
    public static RealVector createRealVector(double[] data)
        throws NoDataException, NullArgumentException {
        if (data == null) {
            throw new NullArgumentException();
        }
        return new ArrayRealVector(data, true);
    }

    /**
     * Creates a {@link FieldVector} using the data from the input array.
     *
     * @param <T> the type of the field elements
     * @param data the input data
     * @return a data.length FieldVector
     * @throws NoDataException if {@code data} is empty.
     * @throws NullArgumentException if {@code data} is {@code null}.
     * @throws ZeroException if {@code data} has 0 elements
     */
    public static <T extends FieldElement<T>> FieldVector<T> createFieldVector(final T[] data)
        throws NoDataException, NullArgumentException, ZeroException {
        if (data == null) {
            throw new NullArgumentException();
        }
        if (data.length == 0) {
            throw new ZeroException(LocalizedFormats.VECTOR_MUST_HAVE_AT_LEAST_ONE_ELEMENT);
        }
        return new ArrayFieldVector<T>(data[0].getField(), data, true);
    }

    /**
     * Create a row {@link RealMatrix} using the data from the input
     * array.
     *
     * @param rowData the input row data
     * @return a 1 x rowData.length RealMatrix
     * @throws NoDataException if {@code rowData} is empty.
     * @throws NullArgumentException if {@code rowData} is {@code null}.
     */
    public static RealMatrix createRowRealMatrix(double[] rowData)
        throws NoDataException, NullArgumentException {
        if (rowData == null) {
            throw new NullArgumentException();
        }
        final int nCols = rowData.length;
        final RealMatrix m = createRealMatrix(1, nCols);
        for (int i = 0; i < nCols; ++i) {
            m.setEntry(0, i, rowData[i]);
        }
        return m;
    }

    /**
     * Create a row {@link FieldMatrix} using the data from the input
     * array.
     *
     * @param <T> the type of the field elements
     * @param rowData the input row data
     * @return a 1 x rowData.length FieldMatrix
     * @throws NoDataException if {@code rowData} is empty.
     * @throws NullArgumentException if {@code rowData} is {@code null}.
     */
    public static <T extends FieldElement<T>> FieldMatrix<T>
        createRowFieldMatrix(final T[] rowData)
        throws NoDataException, NullArgumentException {
        if (rowData == null) {
            throw new NullArgumentException();
        }
        final int nCols = rowData.length;
        if (nCols == 0) {
            throw new NoDataException(LocalizedFormats.AT_LEAST_ONE_COLUMN);
        }
        final FieldMatrix<T> m = createFieldMatrix(rowData[0].getField(), 1, nCols);
        for (int i = 0; i < nCols; ++i) {
            m.setEntry(0, i, rowData[i]);
        }
        return m;
    }

    /**
     * Creates a column {@link RealMatrix} using the data from the input
     * array.
     *
     * @param columnData  the input column data
     * @return a columnData x 1 RealMatrix
     * @throws NoDataException if {@code columnData} is empty.
     * @throws NullArgumentException if {@code columnData} is {@code null}.
     */
    public static RealMatrix createColumnRealMatrix(double[] columnData)
        throws NoDataException, NullArgumentException {
        if (columnData == null) {
            throw new NullArgumentException();
        }
        final int nRows = columnData.length;
        final RealMatrix m = createRealMatrix(nRows, 1);
        for (int i = 0; i < nRows; ++i) {
            m.setEntry(i, 0, columnData[i]);
        }
        return m;
    }

    /**
     * Creates a column {@link FieldMatrix} using the data from the input
     * array.
     *
     * @param <T> the type of the field elements
     * @param columnData  the input column data
     * @return a columnData x 1 FieldMatrix
     * @throws NoDataException if {@code data} is empty.
     * @throws NullArgumentException if {@code columnData} is {@code null}.
     */
    public static <T extends FieldElement<T>> FieldMatrix<T>
        createColumnFieldMatrix(final T[] columnData)
        throws NoDataException, NullArgumentException {
        if (columnData == null) {
            throw new NullArgumentException();
        }
        final int nRows = columnData.length;
        if (nRows == 0) {
            throw new NoDataException(LocalizedFormats.AT_LEAST_ONE_ROW);
        }
        final FieldMatrix<T> m = createFieldMatrix(columnData[0].getField(), nRows, 1);
        for (int i = 0; i < nRows; ++i) {
            m.setEntry(i, 0, columnData[i]);
        }
        return m;
    }

    /**
     * Checks whether a matrix is symmetric, within a given relative tolerance.
     *
     * @param matrix Matrix to check.
     * @param relativeTolerance Tolerance of the symmetry check.
     * @param raiseException If {@code true}, an exception will be raised if
     * the matrix is not symmetric.
     * @return {@code true} if {@code matrix} is symmetric.
     * @throws NonSquareMatrixException if the matrix is not square.
     * @throws NonSymmetricMatrixException if the matrix is not symmetric.
     */
    private static boolean isSymmetricInternal(RealMatrix matrix,
                                               double relativeTolerance,
                                               boolean raiseException) {
        final int rows = matrix.getRowDimension();
        if (rows != matrix.getColumnDimension()) {
            if (raiseException) {
                throw new NonSquareMatrixException(rows, matrix.getColumnDimension());
            } else {
                return false;
            }
        }
        for (int i = 0; i < rows; i++) {
            for (int j = i + 1; j < rows; j++) {
                final double mij = matrix.getEntry(i, j);
                final double mji = matrix.getEntry(j, i);
                if (FastMath.abs(mij - mji) >
                    FastMath.max(FastMath.abs(mij), FastMath.abs(mji)) * relativeTolerance) {
                    if (raiseException) {
                        throw new NonSymmetricMatrixException(i, j, relativeTolerance);
                    } else {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * Checks whether a matrix is symmetric.
     *
     * @param matrix Matrix to check.
     * @param eps Relative tolerance.
     * @throws NonSquareMatrixException if the matrix is not square.
     * @throws NonSymmetricMatrixException if the matrix is not symmetric.
     * @since 3.1
     */
    public static void checkSymmetric(RealMatrix matrix,
                                      double eps) {
        isSymmetricInternal(matrix, eps, true);
    }

    /**
     * Checks whether a matrix is symmetric.
     *
     * @param matrix Matrix to check.
     * @param eps Relative tolerance.
     * @return {@code true} if {@code matrix} is symmetric.
     * @since 3.1
     */
    public static boolean isSymmetric(RealMatrix matrix,
                                      double eps) {
        return isSymmetricInternal(matrix, eps, false);
    }

    /**
     * Check if matrix indices are valid.
     *
     * @param m Matrix.
     * @param row Row index to check.
     * @param column Column index to check.
     * @throws OutOfRangeException if {@code row} or {@code column} is not
     * a valid index.
     */
    public static void checkMatrixIndex(final AnyMatrix m,
                                        final int row, final int column)
        throws OutOfRangeException {
        checkRowIndex(m, row);
        checkColumnIndex(m, column);
    }

    /**
     * Check if a row index is valid.
     *
     * @param m Matrix.
     * @param row Row index to check.
     * @throws OutOfRangeException if {@code row} is not a valid index.
     */
    public static void checkRowIndex(final AnyMatrix m, final int row)
        throws OutOfRangeException {
        if (row < 0 ||
            row >= m.getRowDimension()) {
            throw new OutOfRangeException(LocalizedFormats.ROW_INDEX,
                                          row, 0, m.getRowDimension() - 1);
        }
    }

    /**
     * Check if a column index is valid.
     *
     * @param m Matrix.
     * @param column Column index to check.
     * @throws OutOfRangeException if {@code column} is not a valid index.
     */
    public static void checkColumnIndex(final AnyMatrix m, final int column)
        throws OutOfRangeException {
        if (column < 0 || column >= m.getColumnDimension()) {
            throw new OutOfRangeException(LocalizedFormats.COLUMN_INDEX,
                                           column, 0, m.getColumnDimension() - 1);
        }
    }

    /**
     * Check if submatrix ranges indices are valid.
     * Rows and columns are indicated counting from 0 to {@code n - 1}.
     *
     * @param m Matrix.
     * @param startRow Initial row index.
     * @param endRow Final row index.
     * @param startColumn Initial column index.
     * @param endColumn Final column index.
     * @throws OutOfRangeException if the indices are invalid.
     * @throws NumberIsTooSmallException if {@code endRow < startRow} or
     * {@code endColumn < startColumn}.
     */
    public static void checkSubMatrixIndex(final AnyMatrix m,
                                           final int startRow, final int endRow,
                                           final int startColumn, final int endColumn)
        throws NumberIsTooSmallException, OutOfRangeException {
        checkRowIndex(m, startRow);
        checkRowIndex(m, endRow);
        if (endRow < startRow) {
            throw new NumberIsTooSmallException(LocalizedFormats.INITIAL_ROW_AFTER_FINAL_ROW,
                                                endRow, startRow, false);
        }

        checkColumnIndex(m, startColumn);
        checkColumnIndex(m, endColumn);
        if (endColumn < startColumn) {
            throw new NumberIsTooSmallException(LocalizedFormats.INITIAL_COLUMN_AFTER_FINAL_COLUMN,
                                                endColumn, startColumn, false);
        }


    }

    /**
     * Check if submatrix ranges indices are valid.
     * Rows and columns are indicated counting from 0 to n-1.
     *
     * @param m Matrix.
     * @param selectedRows Array of row indices.
     * @param selectedColumns Array of column indices.
     * @throws NullArgumentException if {@code selectedRows} or
     * {@code selectedColumns} are {@code null}.
     * @throws NoDataException if the row or column selections are empty (zero
     * length).
     * @throws OutOfRangeException if row or column selections are not valid.
     */
    public static void checkSubMatrixIndex(final AnyMatrix m,
                                           final int[] selectedRows,
                                           final int[] selectedColumns)
        throws NoDataException, NullArgumentException, OutOfRangeException {
        if (selectedRows == null) {
            throw new NullArgumentException();
        }
        if (selectedColumns == null) {
            throw new NullArgumentException();
        }
        if (selectedRows.length == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_SELECTED_ROW_INDEX_ARRAY);
        }
        if (selectedColumns.length == 0) {
            throw new NoDataException(LocalizedFormats.EMPTY_SELECTED_COLUMN_INDEX_ARRAY);
        }

        for (final int row : selectedRows) {
            checkRowIndex(m, row);
        }
        for (final int column : selectedColumns) {
            checkColumnIndex(m, column);
        }
    }

    /**
     * Check if matrices are addition compatible.
     *
     * @param left Left hand side matrix.
     * @param right Right hand side matrix.
     * @throws MatrixDimensionMismatchException if the matrices are not addition
     * compatible.
     */
    public static void checkAdditionCompatible(final AnyMatrix left, final AnyMatrix right)
        throws MatrixDimensionMismatchException {
        if ((left.getRowDimension()    != right.getRowDimension()) ||
            (left.getColumnDimension() != right.getColumnDimension())) {
            throw new MatrixDimensionMismatchException(left.getRowDimension(), left.getColumnDimension(),
                                                       right.getRowDimension(), right.getColumnDimension());
        }
    }

    /**
     * Check if matrices are subtraction compatible
     *
     * @param left Left hand side matrix.
     * @param right Right hand side matrix.
     * @throws MatrixDimensionMismatchException if the matrices are not addition
     * compatible.
     */
    public static void checkSubtractionCompatible(final AnyMatrix left, final AnyMatrix right)
        throws MatrixDimensionMismatchException {
        if ((left.getRowDimension()    != right.getRowDimension()) ||
            (left.getColumnDimension() != right.getColumnDimension())) {
            throw new MatrixDimensionMismatchException(left.getRowDimension(), left.getColumnDimension(),
                                                       right.getRowDimension(), right.getColumnDimension());
        }
    }

    /**
     * Check if matrices are multiplication compatible
     *
     * @param left Left hand side matrix.
     * @param right Right hand side matrix.
     * @throws DimensionMismatchException if matrices are not multiplication
     * compatible.
     */
    public static void checkMultiplicationCompatible(final AnyMatrix left, final AnyMatrix right)
        throws DimensionMismatchException {

        if (left.getColumnDimension() != right.getRowDimension()) {
            throw new DimensionMismatchException(left.getColumnDimension(),
                                                 right.getRowDimension());
        }
    }

    /**
     * Convert a {@link FieldMatrix}/{@link Fraction} matrix to a {@link RealMatrix}.
     * @param m Matrix to convert.
     * @return the converted matrix.
     */
    public static Array2DRowRealMatrix fractionMatrixToRealMatrix(final FieldMatrix<Fraction> m) {
        final FractionMatrixConverter converter = new FractionMatrixConverter();
        m.walkInOptimizedOrder(converter);
        return converter.getConvertedMatrix();
    }

    /** Converter for {@link FieldMatrix}/{@link Fraction}. */
    private static class FractionMatrixConverter extends DefaultFieldMatrixPreservingVisitor<Fraction> {
        /** Converted array. */
        private double[][] data;
        /** Simple constructor. */
        FractionMatrixConverter() {
            super(Fraction.ZERO);
        }

        /** {@inheritDoc} */
        @Override
        public void start(int rows, int columns,
                          int startRow, int endRow, int startColumn, int endColumn) {
            data = new double[rows][columns];
        }

        /** {@inheritDoc} */
        @Override
        public void visit(int row, int column, Fraction value) {
            data[row][column] = value.doubleValue();
        }

        /**
         * Get the converted matrix.
         *
         * @return the converted matrix.
         */
        Array2DRowRealMatrix getConvertedMatrix() {
            return new Array2DRowRealMatrix(data, false);
        }

    }

    /**
     * Convert a {@link FieldMatrix}/{@link BigFraction} matrix to a {@link RealMatrix}.
     *
     * @param m Matrix to convert.
     * @return the converted matrix.
     */
    public static Array2DRowRealMatrix bigFractionMatrixToRealMatrix(final FieldMatrix<BigFraction> m) {
        final BigFractionMatrixConverter converter = new BigFractionMatrixConverter();
        m.walkInOptimizedOrder(converter);
        return converter.getConvertedMatrix();
    }

    /** Converter for {@link FieldMatrix}/{@link BigFraction}. */
    private static class BigFractionMatrixConverter extends DefaultFieldMatrixPreservingVisitor<BigFraction> {
        /** Converted array. */
        private double[][] data;
        /** Simple constructor. */
        BigFractionMatrixConverter() {
            super(BigFraction.ZERO);
        }

        /** {@inheritDoc} */
        @Override
        public void start(int rows, int columns,
                          int startRow, int endRow, int startColumn, int endColumn) {
            data = new double[rows][columns];
        }

        /** {@inheritDoc} */
        @Override
        public void visit(int row, int column, BigFraction value) {
            data[row][column] = value.doubleValue();
        }

        /**
         * Get the converted matrix.
         *
         * @return the converted matrix.
         */
        Array2DRowRealMatrix getConvertedMatrix() {
            return new Array2DRowRealMatrix(data, false);
        }
    }

    /** Serialize a {@link RealVector}.
     * <p>
     * This method is intended to be called from within a private
     * <code>writeObject</code> method (after a call to
     * <code>oos.defaultWriteObject()</code>) in a class that has a
     * {@link RealVector} field, which should be declared <code>transient</code>.
     * This way, the default handling does not serialize the vector (the {@link
     * RealVector} interface is not serializable by default) but this method does
     * serialize it specifically.
     * </p>
     * <p>
     * The following example shows how a simple class with a name and a real vector
     * should be written:
     * <pre><code>
     * public class NamedVector implements Serializable {
     *
     *     private final String name;
     *     private final transient RealVector coefficients;
     *
     *     // omitted constructors, getters ...
     *
     *     private void writeObject(ObjectOutputStream oos) throws IOException {
     *         oos.defaultWriteObject();  // takes care of name field
     *         MatrixUtils.serializeRealVector(coefficients, oos);
     *     }
     *
     *     private void readObject(ObjectInputStream ois) throws ClassNotFoundException, IOException {
     *         ois.defaultReadObject();  // takes care of name field
     *         MatrixUtils.deserializeRealVector(this, "coefficients", ois);
     *     }
     *
     * }
     * </code></pre>
     * </p>
     *
     * @param vector real vector to serialize
     * @param oos stream where the real vector should be written
     * @exception IOException if object cannot be written to stream
     * @see #deserializeRealVector(Object, String, ObjectInputStream)
     */
    public static void serializeRealVector(final RealVector vector,
                                           final ObjectOutputStream oos)
        throws IOException {
        final int n = vector.getDimension();
        oos.writeInt(n);
        for (int i = 0; i < n; ++i) {
            oos.writeDouble(vector.getEntry(i));
        }
    }

    /** Deserialize  a {@link RealVector} field in a class.
     * <p>
     * This method is intended to be called from within a private
     * <code>readObject</code> method (after a call to
     * <code>ois.defaultReadObject()</code>) in a class that has a
     * {@link RealVector} field, which should be declared <code>transient</code>.
     * This way, the default handling does not deserialize the vector (the {@link
     * RealVector} interface is not serializable by default) but this method does
     * deserialize it specifically.
     * </p>
     * @param instance instance in which the field must be set up
     * @param fieldName name of the field within the class (may be private and final)
     * @param ois stream from which the real vector should be read
     * @exception ClassNotFoundException if a class in the stream cannot be found
     * @exception IOException if object cannot be read from the stream
     * @see #serializeRealVector(RealVector, ObjectOutputStream)
     */
    public static void deserializeRealVector(final Object instance,
                                             final String fieldName,
                                             final ObjectInputStream ois)
      throws ClassNotFoundException, IOException {
        try {

            // read the vector data
            final int n = ois.readInt();
            final double[] data = new double[n];
            for (int i = 0; i < n; ++i) {
                data[i] = ois.readDouble();
            }

            // create the instance
            final RealVector vector = new ArrayRealVector(data, false);

            // set up the field
            final java.lang.reflect.Field f =
                instance.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(instance, vector);

        } catch (NoSuchFieldException nsfe) {
            IOException ioe = new IOException();
            ioe.initCause(nsfe);
            throw ioe;
        } catch (IllegalAccessException iae) {
            IOException ioe = new IOException();
            ioe.initCause(iae);
            throw ioe;
        }

    }

    /** Serialize a {@link RealMatrix}.
     * <p>
     * This method is intended to be called from within a private
     * <code>writeObject</code> method (after a call to
     * <code>oos.defaultWriteObject()</code>) in a class that has a
     * {@link RealMatrix} field, which should be declared <code>transient</code>.
     * This way, the default handling does not serialize the matrix (the {@link
     * RealMatrix} interface is not serializable by default) but this method does
     * serialize it specifically.
     * </p>
     * <p>
     * The following example shows how a simple class with a name and a real matrix
     * should be written:
     * <pre><code>
     * public class NamedMatrix implements Serializable {
     *
     *     private final String name;
     *     private final transient RealMatrix coefficients;
     *
     *     // omitted constructors, getters ...
     *
     *     private void writeObject(ObjectOutputStream oos) throws IOException {
     *         oos.defaultWriteObject();  // takes care of name field
     *         MatrixUtils.serializeRealMatrix(coefficients, oos);
     *     }
     *
     *     private void readObject(ObjectInputStream ois) throws ClassNotFoundException, IOException {
     *         ois.defaultReadObject();  // takes care of name field
     *         MatrixUtils.deserializeRealMatrix(this, "coefficients", ois);
     *     }
     *
     * }
     * </code></pre>
     * </p>
     *
     * @param matrix real matrix to serialize
     * @param oos stream where the real matrix should be written
     * @exception IOException if object cannot be written to stream
     * @see #deserializeRealMatrix(Object, String, ObjectInputStream)
     */
    public static void serializeRealMatrix(final RealMatrix matrix,
                                           final ObjectOutputStream oos)
        throws IOException {
        final int n = matrix.getRowDimension();
        final int m = matrix.getColumnDimension();
        oos.writeInt(n);
        oos.writeInt(m);
        for (int i = 0; i < n; ++i) {
            for (int j = 0; j < m; ++j) {
                oos.writeDouble(matrix.getEntry(i, j));
            }
        }
    }

    /** Deserialize  a {@link RealMatrix} field in a class.
     * <p>
     * This method is intended to be called from within a private
     * <code>readObject</code> method (after a call to
     * <code>ois.defaultReadObject()</code>) in a class that has a
     * {@link RealMatrix} field, which should be declared <code>transient</code>.
     * This way, the default handling does not deserialize the matrix (the {@link
     * RealMatrix} interface is not serializable by default) but this method does
     * deserialize it specifically.
     * </p>
     * @param instance instance in which the field must be set up
     * @param fieldName name of the field within the class (may be private and final)
     * @param ois stream from which the real matrix should be read
     * @exception ClassNotFoundException if a class in the stream cannot be found
     * @exception IOException if object cannot be read from the stream
     * @see #serializeRealMatrix(RealMatrix, ObjectOutputStream)
     */
    public static void deserializeRealMatrix(final Object instance,
                                             final String fieldName,
                                             final ObjectInputStream ois)
      throws ClassNotFoundException, IOException {
        try {

            // read the matrix data
            final int n = ois.readInt();
            final int m = ois.readInt();
            final double[][] data = new double[n][m];
            for (int i = 0; i < n; ++i) {
                final double[] dataI = data[i];
                for (int j = 0; j < m; ++j) {
                    dataI[j] = ois.readDouble();
                }
            }

            // create the instance
            final RealMatrix matrix = new Array2DRowRealMatrix(data, false);

            // set up the field
            final java.lang.reflect.Field f =
                instance.getClass().getDeclaredField(fieldName);
            f.setAccessible(true);
            f.set(instance, matrix);

        } catch (NoSuchFieldException nsfe) {
            IOException ioe = new IOException();
            ioe.initCause(nsfe);
            throw ioe;
        } catch (IllegalAccessException iae) {
            IOException ioe = new IOException();
            ioe.initCause(iae);
            throw ioe;
        }
    }

    /**Solve  a  system of composed of a Lower Triangular Matrix
     * {@link RealMatrix}.
     * <p>
     * This method is called to solve systems of equations which are
     * of the lower triangular form. The matrix {@link RealMatrix}
     * is assumed, though not checked, to be in lower triangular form.
     * The vector {@link RealVector} is overwritten with the solution.
     * The matrix is checked that it is square and its dimensions match
     * the length of the vector.
     * </p>
     * @param rm RealMatrix which is lower triangular
     * @param b  RealVector this is overwritten
     * @throws DimensionMismatchException if the matrix and vector are not
     * conformable
     * @throws NonSquareMatrixException if the matrix {@code rm} is not square
     * @throws MathArithmeticException if the absolute value of one of the diagonal
     * coefficient of {@code rm} is lower than {@link Precision#SAFE_MIN}
     */
    public static void solveLowerTriangularSystem(RealMatrix rm, RealVector b)
        throws DimensionMismatchException, MathArithmeticException,
        NonSquareMatrixException {
        if ((rm == null) || (b == null) || ( rm.getRowDimension() != b.getDimension())) {
            throw new DimensionMismatchException(
                    (rm == null) ? 0 : rm.getRowDimension(),
                    (b == null) ? 0 : b.getDimension());
        }
        if( rm.getColumnDimension() != rm.getRowDimension() ){
            throw new NonSquareMatrixException(rm.getRowDimension(),
                                               rm.getColumnDimension());
        }
        int rows = rm.getRowDimension();
        for( int i = 0 ; i < rows ; i++ ){
            double diag = rm.getEntry(i, i);
            if( FastMath.abs(diag) < Precision.SAFE_MIN ){
                throw new MathArithmeticException(LocalizedFormats.ZERO_DENOMINATOR);
            }
            double bi = b.getEntry(i)/diag;
            b.setEntry(i,  bi );
            for( int j = i+1; j< rows; j++ ){
                b.setEntry(j, b.getEntry(j)-bi*rm.getEntry(j,i)  );
            }
        }
    }

    /** Solver a  system composed  of an Upper Triangular Matrix
     * {@link RealMatrix}.
     * <p>
     * This method is called to solve systems of equations which are
     * of the lower triangular form. The matrix {@link RealMatrix}
     * is assumed, though not checked, to be in upper triangular form.
     * The vector {@link RealVector} is overwritten with the solution.
     * The matrix is checked that it is square and its dimensions match
     * the length of the vector.
     * </p>
     * @param rm RealMatrix which is upper triangular
     * @param b  RealVector this is overwritten
     * @throws DimensionMismatchException if the matrix and vector are not
     * conformable
     * @throws NonSquareMatrixException if the matrix {@code rm} is not
     * square
     * @throws MathArithmeticException if the absolute value of one of the diagonal
     * coefficient of {@code rm} is lower than {@link Precision#SAFE_MIN}
     */
    public static void solveUpperTriangularSystem(RealMatrix rm, RealVector b)
        throws DimensionMismatchException, MathArithmeticException,
        NonSquareMatrixException {
        if ((rm == null) || (b == null) || ( rm.getRowDimension() != b.getDimension())) {
            throw new DimensionMismatchException(
                    (rm == null) ? 0 : rm.getRowDimension(),
                    (b == null) ? 0 : b.getDimension());
        }
        if( rm.getColumnDimension() != rm.getRowDimension() ){
            throw new NonSquareMatrixException(rm.getRowDimension(),
                                               rm.getColumnDimension());
        }
        int rows = rm.getRowDimension();
        for( int i = rows-1 ; i >-1 ; i-- ){
            double diag = rm.getEntry(i, i);
            if( FastMath.abs(diag) < Precision.SAFE_MIN ){
                throw new MathArithmeticException(LocalizedFormats.ZERO_DENOMINATOR);
            }
            double bi = b.getEntry(i)/diag;
            b.setEntry(i,  bi );
            for( int j = i-1; j>-1; j-- ){
                b.setEntry(j, b.getEntry(j)-bi*rm.getEntry(j,i)  );
            }
        }
    }

    /**
     * Computes the inverse of the given matrix by splitting it into
     * 4 sub-matrices.
     *
     * @param m Matrix whose inverse must be computed.
     * @param splitIndex Index that determines the "split" line and
     * column.
     * The element corresponding to this index will part of the
     * upper-left sub-matrix.
     * @return the inverse of {@code m}.
     * @throws NonSquareMatrixException if {@code m} is not square.
     */
    public static RealMatrix blockInverse(RealMatrix m,
                                          int splitIndex) {
        final int n = m.getRowDimension();
        if (m.getColumnDimension() != n) {
            throw new NonSquareMatrixException(m.getRowDimension(),
                                               m.getColumnDimension());
        }

        final int splitIndex1 = splitIndex + 1;

        final RealMatrix a = m.getSubMatrix(0, splitIndex, 0, splitIndex);
        final RealMatrix b = m.getSubMatrix(0, splitIndex, splitIndex1, n - 1);
        final RealMatrix c = m.getSubMatrix(splitIndex1, n - 1, 0, splitIndex);
        final RealMatrix d = m.getSubMatrix(splitIndex1, n - 1, splitIndex1, n - 1);

        final SingularValueDecomposition aDec = new SingularValueDecomposition(a);
        final DecompositionSolver aSolver = aDec.getSolver();
        if (!aSolver.isNonSingular()) {
            throw new SingularMatrixException();
        }
        final RealMatrix aInv = aSolver.getInverse();

        final SingularValueDecomposition dDec = new SingularValueDecomposition(d);
        final DecompositionSolver dSolver = dDec.getSolver();
        if (!dSolver.isNonSingular()) {
            throw new SingularMatrixException();
        }
        final RealMatrix dInv = dSolver.getInverse();

        final RealMatrix tmp1 = a.subtract(b.multiply(dInv).multiply(c));
        final SingularValueDecomposition tmp1Dec = new SingularValueDecomposition(tmp1);
        final DecompositionSolver tmp1Solver = tmp1Dec.getSolver();
        if (!tmp1Solver.isNonSingular()) {
            throw new SingularMatrixException();
        }
        final RealMatrix result00 = tmp1Solver.getInverse();

        final RealMatrix tmp2 = d.subtract(c.multiply(aInv).multiply(b));
        final SingularValueDecomposition tmp2Dec = new SingularValueDecomposition(tmp2);
        final DecompositionSolver tmp2Solver = tmp2Dec.getSolver();
        if (!tmp2Solver.isNonSingular()) {
            throw new SingularMatrixException();
        }
        final RealMatrix result11 = tmp2Solver.getInverse();

        final RealMatrix result01 = aInv.multiply(b).multiply(result11).scalarMultiply(-1);
        final RealMatrix result10 = dInv.multiply(c).multiply(result00).scalarMultiply(-1);

        final RealMatrix result = new Array2DRowRealMatrix(n, n);
        result.setSubMatrix(result00.getData(), 0, 0);
        result.setSubMatrix(result01.getData(), 0, splitIndex1);
        result.setSubMatrix(result10.getData(), splitIndex1, 0);
        result.setSubMatrix(result11.getData(), splitIndex1, splitIndex1);

        return result;
    }

    /**
     * Computes the inverse of the given matrix.
     * <p>
     * By default, the inverse of the matrix is computed using the QR-decomposition,
     * unless a more efficient method can be determined for the input matrix.
     * <p>
     * Note: this method will use a singularity threshold of 0,
     * use {@link #inverse(RealMatrix, double)} if a different threshold is needed.
     *
     * @param matrix Matrix whose inverse shall be computed
     * @return the inverse of {@code matrix}
     * @throws NullArgumentException if {@code matrix} is {@code null}
     * @throws SingularMatrixException if m is singular
     * @throws NonSquareMatrixException if matrix is not square
     * @since 3.3
     */
    public static RealMatrix inverse(RealMatrix matrix)
            throws NullArgumentException, SingularMatrixException, NonSquareMatrixException {
        return inverse(matrix, 0);
    }

    /**
     * Computes the inverse of the given matrix.
     * <p>
     * By default, the inverse of the matrix is computed using the QR-decomposition,
     * unless a more efficient method can be determined for the input matrix.
     *
     * @param matrix Matrix whose inverse shall be computed
     * @param threshold Singularity threshold
     * @return the inverse of {@code m}
     * @throws NullArgumentException if {@code matrix} is {@code null}
     * @throws SingularMatrixException if matrix is singular
     * @throws NonSquareMatrixException if matrix is not square
     * @since 3.3
     */
    public static RealMatrix inverse(RealMatrix matrix, double threshold)
            throws NullArgumentException, SingularMatrixException, NonSquareMatrixException {

        MathUtils.checkNotNull(matrix);

        if (!matrix.isSquare()) {
            throw new NonSquareMatrixException(matrix.getRowDimension(),
                                               matrix.getColumnDimension());
        }

        if (matrix instanceof DiagonalMatrix) {
            return ((DiagonalMatrix) matrix).inverse(threshold);
        } else {
            QRDecomposition decomposition = new QRDecomposition(matrix, threshold);
            return decomposition.getSolver().getInverse();
        }
    }
}
