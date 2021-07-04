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

import java.util.ArrayList;
import java.util.Locale;

import org.apache.commons.math3.exception.NoDataException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.DimensionMismatchException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.OutOfRangeException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.util.MathUtils;
import org.apache.commons.math3.util.FastMath;

/**
 * Basic implementation of RealMatrix methods regardless of the underlying storage.
 * <p>All the methods implemented here use {@link #getEntry(int, int)} to access
 * matrix elements. Derived class can provide faster implementations.</p>
 *
 * @since 2.0
 */
public abstract class AbstractRealMatrix
    extends RealLinearOperator
    implements RealMatrix {

    /** Default format. */
    private static final RealMatrixFormat DEFAULT_FORMAT = RealMatrixFormat.getInstance(Locale.US);
    static {
        // set the minimum fraction digits to 1 to keep compatibility
        DEFAULT_FORMAT.getFormat().setMinimumFractionDigits(1);
    }

    /**
     * Creates a matrix with no data
     */
    protected AbstractRealMatrix() {}

    /**
     * Create a new RealMatrix with the supplied row and column dimensions.
     *
     * @param rowDimension  the number of rows in the new matrix
     * @param columnDimension  the number of columns in the new matrix
     * @throws NotStrictlyPositiveException if row or column dimension is not positive
     */
    protected AbstractRealMatrix(final int rowDimension,
        final int columnDimension)
        throws NotStrictlyPositiveException {
        if (rowDimension < 1) {
            throw new NotStrictlyPositiveException(rowDimension);
        }
        if (columnDimension < 1) {
            throw new NotStrictlyPositiveException(columnDimension);
        }
    }

    /** {@inheritDoc} */
    public RealMatrix add(RealMatrix m)
        throws MatrixDimensionMismatchException {
        MatrixUtils.checkAdditionCompatible(this, m);

        final int rowCount    = getRowDimension();
        final int columnCount = getColumnDimension();
        final RealMatrix out = createMatrix(rowCount, columnCount);
        for (int row = 0; row < rowCount; ++row) {
            for (int col = 0; col < columnCount; ++col) {
                out.setEntry(row, col, getEntry(row, col) + m.getEntry(row, col));
            }
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealMatrix subtract(final RealMatrix m)
        throws MatrixDimensionMismatchException {
        MatrixUtils.checkSubtractionCompatible(this, m);

        final int rowCount    = getRowDimension();
        final int columnCount = getColumnDimension();
        final RealMatrix out = createMatrix(rowCount, columnCount);
        for (int row = 0; row < rowCount; ++row) {
            for (int col = 0; col < columnCount; ++col) {
                out.setEntry(row, col, getEntry(row, col) - m.getEntry(row, col));
            }
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealMatrix scalarAdd(final double d) {
        final int rowCount    = getRowDimension();
        final int columnCount = getColumnDimension();
        final RealMatrix out = createMatrix(rowCount, columnCount);
        for (int row = 0; row < rowCount; ++row) {
            for (int col = 0; col < columnCount; ++col) {
                out.setEntry(row, col, getEntry(row, col) + d);
            }
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealMatrix scalarMultiply(final double d) {
        final int rowCount    = getRowDimension();
        final int columnCount = getColumnDimension();
        final RealMatrix out = createMatrix(rowCount, columnCount);
        for (int row = 0; row < rowCount; ++row) {
            for (int col = 0; col < columnCount; ++col) {
                out.setEntry(row, col, getEntry(row, col) * d);
            }
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealMatrix multiply(final RealMatrix m)
        throws DimensionMismatchException {
        MatrixUtils.checkMultiplicationCompatible(this, m);

        final int nRows = getRowDimension();
        final int nCols = m.getColumnDimension();
        final int nSum  = getColumnDimension();
        final RealMatrix out = createMatrix(nRows, nCols);
        for (int row = 0; row < nRows; ++row) {
            for (int col = 0; col < nCols; ++col) {
                double sum = 0;
                for (int i = 0; i < nSum; ++i) {
                    sum += getEntry(row, i) * m.getEntry(i, col);
                }
                out.setEntry(row, col, sum);
            }
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealMatrix preMultiply(final RealMatrix m)
        throws DimensionMismatchException {
        return m.multiply(this);
    }

    /** {@inheritDoc} */
    public RealMatrix power(final int p)
        throws NotPositiveException, NonSquareMatrixException {
        if (p < 0) {
            throw new NotPositiveException(LocalizedFormats.NOT_POSITIVE_EXPONENT, p);
        }

        if (!isSquare()) {
            throw new NonSquareMatrixException(getRowDimension(), getColumnDimension());
        }

        if (p == 0) {
            return MatrixUtils.createRealIdentityMatrix(this.getRowDimension());
        }

        if (p == 1) {
            return this.copy();
        }

        final int power = p - 1;

        /*
         * Only log_2(p) operations is used by doing as follows:
         * 5^214 = 5^128 * 5^64 * 5^16 * 5^4 * 5^2
         *
         * In general, the same approach is used for A^p.
         */

        final char[] binaryRepresentation = Integer.toBinaryString(power).toCharArray();
        final ArrayList<Integer> nonZeroPositions = new ArrayList<Integer>();
        int maxI = -1;

        for (int i = 0; i < binaryRepresentation.length; ++i) {
            if (binaryRepresentation[i] == '1') {
                final int pos = binaryRepresentation.length - i - 1;
                nonZeroPositions.add(pos);

                // The positions are taken in turn, so maxI is only changed once
                if (maxI == -1) {
                    maxI = pos;
                }
            }
        }

        RealMatrix[] results = new RealMatrix[maxI + 1];
        results[0] = this.copy();

        for (int i = 1; i <= maxI; ++i) {
            results[i] = results[i-1].multiply(results[i-1]);
        }

        RealMatrix result = this.copy();

        for (Integer i : nonZeroPositions) {
            result = result.multiply(results[i]);
        }

        return result;
    }

    /** {@inheritDoc} */
    public double[][] getData() {
        final double[][] data = new double[getRowDimension()][getColumnDimension()];

        for (int i = 0; i < data.length; ++i) {
            final double[] dataI = data[i];
            for (int j = 0; j < dataI.length; ++j) {
                dataI[j] = getEntry(i, j);
            }
        }

        return data;
    }

    /** {@inheritDoc} */
    public double getNorm() {
        return walkInColumnOrder(new RealMatrixPreservingVisitor() {

            /** Last row index. */
            private double endRow;

            /** Sum of absolute values on one column. */
            private double columnSum;

            /** Maximal sum across all columns. */
            private double maxColSum;

            /** {@inheritDoc} */
            public void start(final int rows, final int columns,
                              final int startRow, final int endRow,
                              final int startColumn, final int endColumn) {
                this.endRow = endRow;
                columnSum   = 0;
                maxColSum   = 0;
            }

            /** {@inheritDoc} */
            public void visit(final int row, final int column, final double value) {
                columnSum += FastMath.abs(value);
                if (row == endRow) {
                    maxColSum = FastMath.max(maxColSum, columnSum);
                    columnSum = 0;
                }
            }

            /** {@inheritDoc} */
            public double end() {
                return maxColSum;
            }
        });
    }

    /** {@inheritDoc} */
    public double getFrobeniusNorm() {
        return walkInOptimizedOrder(new RealMatrixPreservingVisitor() {

            /** Sum of squared entries. */
            private double sum;

            /** {@inheritDoc} */
            public void start(final int rows, final int columns,
                              final int startRow, final int endRow,
                              final int startColumn, final int endColumn) {
                sum = 0;
            }

            /** {@inheritDoc} */
            public void visit(final int row, final int column, final double value) {
                sum += value * value;
            }

            /** {@inheritDoc} */
            public double end() {
                return FastMath.sqrt(sum);
            }
        });
    }

    /** {@inheritDoc} */
    public RealMatrix getSubMatrix(final int startRow, final int endRow,
                                   final int startColumn, final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);

        final RealMatrix subMatrix =
            createMatrix(endRow - startRow + 1, endColumn - startColumn + 1);
        for (int i = startRow; i <= endRow; ++i) {
            for (int j = startColumn; j <= endColumn; ++j) {
                subMatrix.setEntry(i - startRow, j - startColumn, getEntry(i, j));
            }
        }

        return subMatrix;
    }

    /** {@inheritDoc} */
    public RealMatrix getSubMatrix(final int[] selectedRows,
                                   final int[] selectedColumns)
        throws NullArgumentException, NoDataException, OutOfRangeException {
        MatrixUtils.checkSubMatrixIndex(this, selectedRows, selectedColumns);

        final RealMatrix subMatrix =
            createMatrix(selectedRows.length, selectedColumns.length);
        subMatrix.walkInOptimizedOrder(new DefaultRealMatrixChangingVisitor() {

            /** {@inheritDoc} */
            @Override
            public double visit(final int row, final int column, final double value) {
                return getEntry(selectedRows[row], selectedColumns[column]);
            }

        });

        return subMatrix;
    }

    /** {@inheritDoc} */
    public void copySubMatrix(final int startRow, final int endRow,
                              final int startColumn, final int endColumn,
                              final double[][] destination)
        throws OutOfRangeException, NumberIsTooSmallException,
        MatrixDimensionMismatchException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);
        final int rowsCount    = endRow + 1 - startRow;
        final int columnsCount = endColumn + 1 - startColumn;
        if ((destination.length < rowsCount) || (destination[0].length < columnsCount)) {
            throw new MatrixDimensionMismatchException(destination.length, destination[0].length,
                                                       rowsCount, columnsCount);
        }

        for (int i = 1; i < rowsCount; i++) {
            if (destination[i].length < columnsCount) {
                throw new MatrixDimensionMismatchException(destination.length, destination[i].length,
                                                           rowsCount, columnsCount);
            }
        }

        walkInOptimizedOrder(new DefaultRealMatrixPreservingVisitor() {

            /** Initial row index. */
            private int startRow;

            /** Initial column index. */
            private int startColumn;

            /** {@inheritDoc} */
            @Override
            public void start(final int rows, final int columns,
                              final int startRow, final int endRow,
                              final int startColumn, final int endColumn) {
                this.startRow    = startRow;
                this.startColumn = startColumn;
            }

            /** {@inheritDoc} */
            @Override
            public void visit(final int row, final int column, final double value) {
                destination[row - startRow][column - startColumn] = value;
            }

        }, startRow, endRow, startColumn, endColumn);
    }

    /** {@inheritDoc} */
    public void copySubMatrix(int[] selectedRows, int[] selectedColumns,
                              double[][] destination)
        throws OutOfRangeException, NullArgumentException, NoDataException,
        MatrixDimensionMismatchException {
        MatrixUtils.checkSubMatrixIndex(this, selectedRows, selectedColumns);
        final int nCols = selectedColumns.length;
        if ((destination.length < selectedRows.length) ||
            (destination[0].length < nCols)) {
            throw new MatrixDimensionMismatchException(destination.length, destination[0].length,
                                                       selectedRows.length, selectedColumns.length);
        }

        for (int i = 0; i < selectedRows.length; i++) {
            final double[] destinationI = destination[i];
            if (destinationI.length < nCols) {
                throw new MatrixDimensionMismatchException(destination.length, destinationI.length,
                                                           selectedRows.length, selectedColumns.length);
            }
            for (int j = 0; j < selectedColumns.length; j++) {
                destinationI[j] = getEntry(selectedRows[i], selectedColumns[j]);
            }
        }
    }

    /** {@inheritDoc} */
    public void setSubMatrix(final double[][] subMatrix, final int row, final int column)
        throws NoDataException, OutOfRangeException,
        DimensionMismatchException, NullArgumentException {
        MathUtils.checkNotNull(subMatrix);
        final int nRows = subMatrix.length;
        if (nRows == 0) {
            throw new NoDataException(LocalizedFormats.AT_LEAST_ONE_ROW);
        }

        final int nCols = subMatrix[0].length;
        if (nCols == 0) {
            throw new NoDataException(LocalizedFormats.AT_LEAST_ONE_COLUMN);
        }

        for (int r = 1; r < nRows; ++r) {
            if (subMatrix[r].length != nCols) {
                throw new DimensionMismatchException(nCols, subMatrix[r].length);
            }
        }

        MatrixUtils.checkRowIndex(this, row);
        MatrixUtils.checkColumnIndex(this, column);
        MatrixUtils.checkRowIndex(this, nRows + row - 1);
        MatrixUtils.checkColumnIndex(this, nCols + column - 1);

        for (int i = 0; i < nRows; ++i) {
            for (int j = 0; j < nCols; ++j) {
                setEntry(row + i, column + j, subMatrix[i][j]);
            }
        }
    }

    /** {@inheritDoc} */
    public RealMatrix getRowMatrix(final int row) throws OutOfRangeException {
        MatrixUtils.checkRowIndex(this, row);
        final int nCols = getColumnDimension();
        final RealMatrix out = createMatrix(1, nCols);
        for (int i = 0; i < nCols; ++i) {
            out.setEntry(0, i, getEntry(row, i));
        }

        return out;
    }

    /** {@inheritDoc} */
    public void setRowMatrix(final int row, final RealMatrix matrix)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkRowIndex(this, row);
        final int nCols = getColumnDimension();
        if ((matrix.getRowDimension() != 1) ||
            (matrix.getColumnDimension() != nCols)) {
            throw new MatrixDimensionMismatchException(matrix.getRowDimension(),
                                                       matrix.getColumnDimension(),
                                                       1, nCols);
        }
        for (int i = 0; i < nCols; ++i) {
            setEntry(row, i, matrix.getEntry(0, i));
        }
    }

    /** {@inheritDoc} */
    public RealMatrix getColumnMatrix(final int column)
        throws OutOfRangeException {
        MatrixUtils.checkColumnIndex(this, column);
        final int nRows = getRowDimension();
        final RealMatrix out = createMatrix(nRows, 1);
        for (int i = 0; i < nRows; ++i) {
            out.setEntry(i, 0, getEntry(i, column));
        }

        return out;
    }

    /** {@inheritDoc} */
    public void setColumnMatrix(final int column, final RealMatrix matrix)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkColumnIndex(this, column);
        final int nRows = getRowDimension();
        if ((matrix.getRowDimension() != nRows) ||
            (matrix.getColumnDimension() != 1)) {
            throw new MatrixDimensionMismatchException(matrix.getRowDimension(),
                                                       matrix.getColumnDimension(),
                                                       nRows, 1);
        }
        for (int i = 0; i < nRows; ++i) {
            setEntry(i, column, matrix.getEntry(i, 0));
        }
    }

    /** {@inheritDoc} */
    public RealVector getRowVector(final int row)
        throws OutOfRangeException {
        return new ArrayRealVector(getRow(row), false);
    }

    /** {@inheritDoc} */
    public void setRowVector(final int row, final RealVector vector)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkRowIndex(this, row);
        final int nCols = getColumnDimension();
        if (vector.getDimension() != nCols) {
            throw new MatrixDimensionMismatchException(1, vector.getDimension(),
                                                       1, nCols);
        }
        for (int i = 0; i < nCols; ++i) {
            setEntry(row, i, vector.getEntry(i));
        }
    }

    /** {@inheritDoc} */
    public RealVector getColumnVector(final int column)
        throws OutOfRangeException {
        return new ArrayRealVector(getColumn(column), false);
    }

    /** {@inheritDoc} */
    public void setColumnVector(final int column, final RealVector vector)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkColumnIndex(this, column);
        final int nRows = getRowDimension();
        if (vector.getDimension() != nRows) {
            throw new MatrixDimensionMismatchException(vector.getDimension(), 1,
                                                       nRows, 1);
        }
        for (int i = 0; i < nRows; ++i) {
            setEntry(i, column, vector.getEntry(i));
        }
    }

    /** {@inheritDoc} */
    public double[] getRow(final int row) throws OutOfRangeException {
        MatrixUtils.checkRowIndex(this, row);
        final int nCols = getColumnDimension();
        final double[] out = new double[nCols];
        for (int i = 0; i < nCols; ++i) {
            out[i] = getEntry(row, i);
        }

        return out;
    }

    /** {@inheritDoc} */
    public void setRow(final int row, final double[] array)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkRowIndex(this, row);
        final int nCols = getColumnDimension();
        if (array.length != nCols) {
            throw new MatrixDimensionMismatchException(1, array.length, 1, nCols);
        }
        for (int i = 0; i < nCols; ++i) {
            setEntry(row, i, array[i]);
        }
    }

    /** {@inheritDoc} */
    public double[] getColumn(final int column) throws OutOfRangeException {
        MatrixUtils.checkColumnIndex(this, column);
        final int nRows = getRowDimension();
        final double[] out = new double[nRows];
        for (int i = 0; i < nRows; ++i) {
            out[i] = getEntry(i, column);
        }

        return out;
    }

    /** {@inheritDoc} */
    public void setColumn(final int column, final double[] array)
        throws OutOfRangeException, MatrixDimensionMismatchException {
        MatrixUtils.checkColumnIndex(this, column);
        final int nRows = getRowDimension();
        if (array.length != nRows) {
            throw new MatrixDimensionMismatchException(array.length, 1, nRows, 1);
        }
        for (int i = 0; i < nRows; ++i) {
            setEntry(i, column, array[i]);
        }
    }

    /** {@inheritDoc} */
    public void addToEntry(int row, int column, double increment)
        throws OutOfRangeException {
        MatrixUtils.checkMatrixIndex(this, row, column);
        setEntry(row, column, getEntry(row, column) + increment);
    }

    /** {@inheritDoc} */
    public void multiplyEntry(int row, int column, double factor)
        throws OutOfRangeException {
        MatrixUtils.checkMatrixIndex(this, row, column);
        setEntry(row, column, getEntry(row, column) * factor);
    }

    /** {@inheritDoc} */
    public RealMatrix transpose() {
        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        final RealMatrix out = createMatrix(nCols, nRows);
        walkInOptimizedOrder(new DefaultRealMatrixPreservingVisitor() {

            /** {@inheritDoc} */
            @Override
            public void visit(final int row, final int column, final double value) {
                out.setEntry(column, row, value);
            }

        });

        return out;
    }

    /** {@inheritDoc} */
    public boolean isSquare() {
        return getColumnDimension() == getRowDimension();
    }

    /**
     * Returns the number of rows of this matrix.
     *
     * @return the number of rows.
     */
    @Override
    public abstract int getRowDimension();

    /**
     * Returns the number of columns of this matrix.
     *
     * @return the number of columns.
     */
    @Override
    public abstract int getColumnDimension();

    /** {@inheritDoc} */
    public double getTrace() throws NonSquareMatrixException {
        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        if (nRows != nCols) {
            throw new NonSquareMatrixException(nRows, nCols);
       }
        double trace = 0;
        for (int i = 0; i < nRows; ++i) {
            trace += getEntry(i, i);
        }
        return trace;
    }

    /** {@inheritDoc} */
    public double[] operate(final double[] v)
        throws DimensionMismatchException {
        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        if (v.length != nCols) {
            throw new DimensionMismatchException(v.length, nCols);
        }

        final double[] out = new double[nRows];
        for (int row = 0; row < nRows; ++row) {
            double sum = 0;
            for (int i = 0; i < nCols; ++i) {
                sum += getEntry(row, i) * v[i];
            }
            out[row] = sum;
        }

        return out;
    }

    /** {@inheritDoc} */
    @Override
    public RealVector operate(final RealVector v)
        throws DimensionMismatchException {
        try {
            return new ArrayRealVector(operate(((ArrayRealVector) v).getDataRef()), false);
        } catch (ClassCastException cce) {
            final int nRows = getRowDimension();
            final int nCols = getColumnDimension();
            if (v.getDimension() != nCols) {
                throw new DimensionMismatchException(v.getDimension(), nCols);
            }

            final double[] out = new double[nRows];
            for (int row = 0; row < nRows; ++row) {
                double sum = 0;
                for (int i = 0; i < nCols; ++i) {
                    sum += getEntry(row, i) * v.getEntry(i);
                }
                out[row] = sum;
            }

            return new ArrayRealVector(out, false);
        }
    }

    /** {@inheritDoc} */
    public double[] preMultiply(final double[] v) throws DimensionMismatchException {

        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        if (v.length != nRows) {
            throw new DimensionMismatchException(v.length, nRows);
        }

        final double[] out = new double[nCols];
        for (int col = 0; col < nCols; ++col) {
            double sum = 0;
            for (int i = 0; i < nRows; ++i) {
                sum += getEntry(i, col) * v[i];
            }
            out[col] = sum;
        }

        return out;
    }

    /** {@inheritDoc} */
    public RealVector preMultiply(final RealVector v) throws DimensionMismatchException {
        try {
            return new ArrayRealVector(preMultiply(((ArrayRealVector) v).getDataRef()), false);
        } catch (ClassCastException cce) {

            final int nRows = getRowDimension();
            final int nCols = getColumnDimension();
            if (v.getDimension() != nRows) {
                throw new DimensionMismatchException(v.getDimension(), nRows);
            }

            final double[] out = new double[nCols];
            for (int col = 0; col < nCols; ++col) {
                double sum = 0;
                for (int i = 0; i < nRows; ++i) {
                    sum += getEntry(i, col) * v.getEntry(i);
                }
                out[col] = sum;
            }

            return new ArrayRealVector(out, false);
        }
    }

    /** {@inheritDoc} */
    public double walkInRowOrder(final RealMatrixChangingVisitor visitor) {
        final int rows    = getRowDimension();
        final int columns = getColumnDimension();
        visitor.start(rows, columns, 0, rows - 1, 0, columns - 1);
        for (int row = 0; row < rows; ++row) {
            for (int column = 0; column < columns; ++column) {
                final double oldValue = getEntry(row, column);
                final double newValue = visitor.visit(row, column, oldValue);
                setEntry(row, column, newValue);
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInRowOrder(final RealMatrixPreservingVisitor visitor) {
        final int rows    = getRowDimension();
        final int columns = getColumnDimension();
        visitor.start(rows, columns, 0, rows - 1, 0, columns - 1);
        for (int row = 0; row < rows; ++row) {
            for (int column = 0; column < columns; ++column) {
                visitor.visit(row, column, getEntry(row, column));
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInRowOrder(final RealMatrixChangingVisitor visitor,
                                 final int startRow, final int endRow,
                                 final int startColumn, final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);
        visitor.start(getRowDimension(), getColumnDimension(),
                      startRow, endRow, startColumn, endColumn);
        for (int row = startRow; row <= endRow; ++row) {
            for (int column = startColumn; column <= endColumn; ++column) {
                final double oldValue = getEntry(row, column);
                final double newValue = visitor.visit(row, column, oldValue);
                setEntry(row, column, newValue);
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInRowOrder(final RealMatrixPreservingVisitor visitor,
                                 final int startRow, final int endRow,
                                 final int startColumn, final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);
        visitor.start(getRowDimension(), getColumnDimension(),
                      startRow, endRow, startColumn, endColumn);
        for (int row = startRow; row <= endRow; ++row) {
            for (int column = startColumn; column <= endColumn; ++column) {
                visitor.visit(row, column, getEntry(row, column));
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInColumnOrder(final RealMatrixChangingVisitor visitor) {
        final int rows    = getRowDimension();
        final int columns = getColumnDimension();
        visitor.start(rows, columns, 0, rows - 1, 0, columns - 1);
        for (int column = 0; column < columns; ++column) {
            for (int row = 0; row < rows; ++row) {
                final double oldValue = getEntry(row, column);
                final double newValue = visitor.visit(row, column, oldValue);
                setEntry(row, column, newValue);
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInColumnOrder(final RealMatrixPreservingVisitor visitor) {
        final int rows    = getRowDimension();
        final int columns = getColumnDimension();
        visitor.start(rows, columns, 0, rows - 1, 0, columns - 1);
        for (int column = 0; column < columns; ++column) {
            for (int row = 0; row < rows; ++row) {
                visitor.visit(row, column, getEntry(row, column));
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInColumnOrder(final RealMatrixChangingVisitor visitor,
                                    final int startRow, final int endRow,
                                    final int startColumn, final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);
        visitor.start(getRowDimension(), getColumnDimension(),
                      startRow, endRow, startColumn, endColumn);
        for (int column = startColumn; column <= endColumn; ++column) {
            for (int row = startRow; row <= endRow; ++row) {
                final double oldValue = getEntry(row, column);
                final double newValue = visitor.visit(row, column, oldValue);
                setEntry(row, column, newValue);
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInColumnOrder(final RealMatrixPreservingVisitor visitor,
                                    final int startRow, final int endRow,
                                    final int startColumn, final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        MatrixUtils.checkSubMatrixIndex(this, startRow, endRow, startColumn, endColumn);
        visitor.start(getRowDimension(), getColumnDimension(),
                      startRow, endRow, startColumn, endColumn);
        for (int column = startColumn; column <= endColumn; ++column) {
            for (int row = startRow; row <= endRow; ++row) {
                visitor.visit(row, column, getEntry(row, column));
            }
        }
        return visitor.end();
    }

    /** {@inheritDoc} */
    public double walkInOptimizedOrder(final RealMatrixChangingVisitor visitor) {
        return walkInRowOrder(visitor);
    }

    /** {@inheritDoc} */
    public double walkInOptimizedOrder(final RealMatrixPreservingVisitor visitor) {
        return walkInRowOrder(visitor);
    }

    /** {@inheritDoc} */
    public double walkInOptimizedOrder(final RealMatrixChangingVisitor visitor,
                                       final int startRow, final int endRow,
                                       final int startColumn,
                                       final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        return walkInRowOrder(visitor, startRow, endRow, startColumn, endColumn);
    }

    /** {@inheritDoc} */
    public double walkInOptimizedOrder(final RealMatrixPreservingVisitor visitor,
                                       final int startRow, final int endRow,
                                       final int startColumn,
                                       final int endColumn)
        throws OutOfRangeException, NumberIsTooSmallException {
        return walkInRowOrder(visitor, startRow, endRow, startColumn, endColumn);
    }

    /**
     * Get a string representation for this matrix.
     * @return a string representation for this matrix
     */
    @Override
    public String toString() {
        final StringBuilder res = new StringBuilder();
        String fullClassName = getClass().getName();
        String shortClassName = fullClassName.substring(fullClassName.lastIndexOf('.') + 1);
        res.append(shortClassName);
        res.append(DEFAULT_FORMAT.format(this));
        return res.toString();
    }

    /**
     * Returns true iff <code>object</code> is a
     * <code>RealMatrix</code> instance with the same dimensions as this
     * and all corresponding matrix entries are equal.
     *
     * @param object the object to test equality against.
     * @return true if object equals this
     */
    @Override
    public boolean equals(final Object object) {
        if (object == this ) {
            return true;
        }
        if (object instanceof RealMatrix == false) {
            return false;
        }
        RealMatrix m = (RealMatrix) object;
        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        if (m.getColumnDimension() != nCols || m.getRowDimension() != nRows) {
            return false;
        }
        for (int row = 0; row < nRows; ++row) {
            for (int col = 0; col < nCols; ++col) {
                if (getEntry(row, col) != m.getEntry(row, col)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Computes a hashcode for the matrix.
     *
     * @return hashcode for matrix
     */
    @Override
    public int hashCode() {
        int ret = 7;
        final int nRows = getRowDimension();
        final int nCols = getColumnDimension();
        ret = ret * 31 + nRows;
        ret = ret * 31 + nCols;
        for (int row = 0; row < nRows; ++row) {
            for (int col = 0; col < nCols; ++col) {
               ret = ret * 31 + (11 * (row+1) + 17 * (col+1)) *
                   MathUtils.hash(getEntry(row, col));
           }
        }
        return ret;
    }


    /*
     * Empty implementations of these methods are provided in order to allow for
     * the use of the @Override tag with Java 1.5.
     */

    /** {@inheritDoc} */
    public abstract RealMatrix createMatrix(int rowDimension, int columnDimension)
        throws NotStrictlyPositiveException;

    /** {@inheritDoc} */
    public abstract RealMatrix copy();

    /** {@inheritDoc} */
    public abstract double getEntry(int row, int column)
        throws OutOfRangeException;

    /** {@inheritDoc} */
    public abstract void setEntry(int row, int column, double value)
        throws OutOfRangeException;
}
