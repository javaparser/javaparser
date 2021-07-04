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

import org.apache.commons.math3.FieldElement;


/**
 * Interface handling decomposition algorithms that can solve A &times; X = B.
 * <p>Decomposition algorithms decompose an A matrix has a product of several specific
 * matrices from which they can solve A &times; X = B in least squares sense: they find X
 * such that ||A &times; X - B|| is minimal.</p>
 * <p>Some solvers like {@link FieldLUDecomposition} can only find the solution for
 * square matrices and when the solution is an exact linear solution, i.e. when
 * ||A &times; X - B|| is exactly 0. Other solvers can also find solutions
 * with non-square matrix A and with non-null minimal norm. If an exact linear
 * solution exists it is also the minimal norm solution.</p>
 *
 * @param <T> the type of the field elements
 * @since 2.0
 */
public interface FieldDecompositionSolver<T extends FieldElement<T>> {

    /** Solve the linear equation A &times; X = B for matrices A.
     * <p>The A matrix is implicit, it is provided by the underlying
     * decomposition algorithm.</p>
     * @param b right-hand side of the equation A &times; X = B
     * @return a vector X that minimizes the two norm of A &times; X - B
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the matrices dimensions do not match.
     * @throws SingularMatrixException
     * if the decomposed matrix is singular.
     */
    FieldVector<T> solve(final FieldVector<T> b);

    /** Solve the linear equation A &times; X = B for matrices A.
     * <p>The A matrix is implicit, it is provided by the underlying
     * decomposition algorithm.</p>
     * @param b right-hand side of the equation A &times; X = B
     * @return a matrix X that minimizes the two norm of A &times; X - B
     * @throws org.apache.commons.math3.exception.DimensionMismatchException
     * if the matrices dimensions do not match.
     * @throws SingularMatrixException
     * if the decomposed matrix is singular.
     */
    FieldMatrix<T> solve(final FieldMatrix<T> b);

    /**
     * Check if the decomposed matrix is non-singular.
     * @return true if the decomposed matrix is non-singular
     */
    boolean isNonSingular();

    /** Get the inverse (or pseudo-inverse) of the decomposed matrix.
     * @return inverse matrix
     * @throws SingularMatrixException
     * if the decomposed matrix is singular.
     */
    FieldMatrix<T> getInverse();
}
