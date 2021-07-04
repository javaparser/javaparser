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
import org.apache.commons.math3.exception.MathArithmeticException;
import org.apache.commons.math3.exception.NotPositiveException;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.OutOfRangeException;

/**
 * Interface defining a field-valued vector with basic algebraic operations.
 * <p>
 * vector element indexing is 0-based -- e.g., <code>getEntry(0)</code>
 * returns the first element of the vector.
 * </p>
 * <p>
 * The various <code>mapXxx</code> and <code>mapXxxToSelf</code> methods operate
 * on vectors element-wise, i.e. they perform the same operation (adding a scalar,
 * applying a function ...) on each element in turn. The <code>mapXxx</code>
 * versions create a new vector to hold the result and do not change the instance.
 * The <code>mapXxxToSelf</code> versions use the instance itself to store the
 * results, so the instance is changed by these methods. In both cases, the result
 * vector is returned by the methods, this allows to use the <i>fluent API</i>
 * style, like this:
 * </p>
 * <pre>
 *   RealVector result = v.mapAddToSelf(3.0).mapTanToSelf().mapSquareToSelf();
 * </pre>
 * <p>
 * Note that as almost all operations on {@link FieldElement} throw {@link
 * NullArgumentException} when operating on a null element, it is the responsibility
 * of <code>FieldVector</code> implementations to make sure no null elements
 * are inserted into the vector. This must be done in all constructors and
 * all setters.
 * <p>
 *
 * @param <T> the type of the field elements
 * @since 2.0
 */
public interface FieldVector<T extends FieldElement<T>>  {

    /**
     * Get the type of field elements of the vector.
     * @return type of field elements of the vector
     */ //@ non_null
    Field<T> getField();

    /**
     * Returns a (deep) copy of this.
     * @return vector copy
     */
    FieldVector<T> copy();

    /**
     * Compute the sum of {@code this} and {@code v}.
     * @param v vector to be added
     * @return {@code this + v}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     */
    FieldVector<T> add(FieldVector<T> v) throws DimensionMismatchException;

    /**
     * Compute {@code this} minus {@code v}.
     * @param v vector to be subtracted
     * @return {@code this - v}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     */
    FieldVector<T> subtract(FieldVector<T> v) throws DimensionMismatchException;

    /**
     * Map an addition operation to each entry.
     * @param d value to be added to each entry
     * @return {@code this + d}
     * @throws NullArgumentException if {@code d} is {@code null}.
     */
    FieldVector<T> mapAdd(T d) throws NullArgumentException;

    /**
     * Map an addition operation to each entry.
     * <p>The instance <strong>is</strong> changed by this method.</p>
     * @param d value to be added to each entry
     * @return for convenience, return {@code this}
     * @throws NullArgumentException if {@code d} is {@code null}.
     */
    FieldVector<T> mapAddToSelf(T d) throws NullArgumentException;

    /**
     * Map a subtraction operation to each entry.
     * @param d value to be subtracted to each entry
     * @return {@code this - d}
     * @throws NullArgumentException if {@code d} is {@code null}
     */
    FieldVector<T> mapSubtract(T d) throws NullArgumentException;

    /**
     * Map a subtraction operation to each entry.
     * <p>The instance <strong>is</strong> changed by this method.</p>
     * @param d value to be subtracted to each entry
     * @return for convenience, return {@code this}
     * @throws NullArgumentException if {@code d} is {@code null}
     */
    FieldVector<T> mapSubtractToSelf(T d) throws NullArgumentException;

    /**
     * Map a multiplication operation to each entry.
     * @param d value to multiply all entries by
     * @return {@code this * d}
     * @throws NullArgumentException if {@code d} is {@code null}.
     */
    FieldVector<T> mapMultiply(T d) throws NullArgumentException;

    /**
     * Map a multiplication operation to each entry.
     * <p>The instance <strong>is</strong> changed by this method.</p>
     * @param d value to multiply all entries by
     * @return for convenience, return {@code this}
     * @throws NullArgumentException if {@code d} is {@code null}.
     */
    FieldVector<T> mapMultiplyToSelf(T d) throws NullArgumentException;

    /**
     * Map a division operation to each entry.
     * @param d value to divide all entries by
     * @return {@code this / d}
     * @throws NullArgumentException if {@code d} is {@code null}.
     * @throws MathArithmeticException if {@code d} is zero.
     */
    FieldVector<T> mapDivide(T d)
        throws NullArgumentException, MathArithmeticException;

    /**
     * Map a division operation to each entry.
     * <p>The instance <strong>is</strong> changed by this method.</p>
     * @param d value to divide all entries by
     * @return for convenience, return {@code this}
     * @throws NullArgumentException if {@code d} is {@code null}.
     * @throws MathArithmeticException if {@code d} is zero.
     */
    FieldVector<T> mapDivideToSelf(T d)
        throws NullArgumentException, MathArithmeticException;

    /**
     * Map the 1/x function to each entry.
     * @return a vector containing the result of applying the function to each entry.
     * @throws MathArithmeticException if one of the entries is zero.
     */
    FieldVector<T> mapInv() throws MathArithmeticException;

    /**
     * Map the 1/x function to each entry.
     * <p>The instance <strong>is</strong> changed by this method.</p>
     * @return for convenience, return {@code this}
     * @throws MathArithmeticException if one of the entries is zero.
     */
    FieldVector<T> mapInvToSelf() throws MathArithmeticException;

    /**
     * Element-by-element multiplication.
     * @param v vector by which instance elements must be multiplied
     * @return a vector containing {@code this[i] * v[i]} for all {@code i}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     */
    FieldVector<T> ebeMultiply(FieldVector<T> v)
        throws DimensionMismatchException;

    /**
     * Element-by-element division.
     * @param v vector by which instance elements must be divided
     * @return a vector containing {@code this[i] / v[i]} for all {@code i}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     * @throws MathArithmeticException if one entry of {@code v} is zero.
     */
    FieldVector<T> ebeDivide(FieldVector<T> v)
        throws DimensionMismatchException, MathArithmeticException;

    /**
     * Returns vector entries as a T array.
     * @return T array of entries
     * @deprecated as of 3.1, to be removed in 4.0. Please use the {@link #toArray()} method instead.
     */
    @Deprecated
    T[] getData();

    /**
     * Compute the dot product.
     * @param v vector with which dot product should be computed
     * @return the scalar dot product of {@code this} and {@code v}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     */
    T dotProduct(FieldVector<T> v) throws DimensionMismatchException;

    /**
     * Find the orthogonal projection of this vector onto another vector.
     * @param v vector onto which {@code this} must be projected
     * @return projection of {@code this} onto {@code v}
     * @throws DimensionMismatchException if {@code v} is not the same size as {@code this}
     * @throws MathArithmeticException if {@code v} is the null vector.
     */
    FieldVector<T> projection(FieldVector<T> v)
        throws DimensionMismatchException, MathArithmeticException;

    /**
     * Compute the outer product.
     * @param v vector with which outer product should be computed
     * @return the matrix outer product between instance and v
     */
    FieldMatrix<T> outerProduct(FieldVector<T> v);

    /**
     * Returns the entry in the specified index.
     *
     * @param index Index location of entry to be fetched.
     * @return the vector entry at {@code index}.
     * @throws OutOfRangeException if the index is not valid.
     * @see #setEntry(int, FieldElement)
     */
    T getEntry(int index) throws OutOfRangeException;

    /**
     * Set a single element.
     * @param index element index.
     * @param value new value for the element.
     * @throws OutOfRangeException if the index is not valid.
     * @see #getEntry(int)
     */
    void setEntry(int index, T value) throws OutOfRangeException;

    /**
     * Returns the size of the vector.
     * @return size
     */
    int getDimension();

    /**
     * Construct a vector by appending a vector to this vector.
     * @param v vector to append to this one.
     * @return a new vector
     */
    FieldVector<T> append(FieldVector<T> v);

    /**
     * Construct a vector by appending a T to this vector.
     * @param d T to append.
     * @return a new vector
     */
    FieldVector<T> append(T d);

    /**
     * Get a subvector from consecutive elements.
     * @param index index of first element.
     * @param n number of elements to be retrieved.
     * @return a vector containing n elements.
     * @throws OutOfRangeException if the index is not valid.
     * @throws NotPositiveException if the number of elements if not positive.
     */
    FieldVector<T> getSubVector(int index, int n)
        throws OutOfRangeException, NotPositiveException;

    /**
     * Set a set of consecutive elements.
     * @param index index of first element to be set.
     * @param v vector containing the values to set.
     * @throws OutOfRangeException if the index is not valid.
     */
    void setSubVector(int index, FieldVector<T> v) throws OutOfRangeException;

    /**
     * Set all elements to a single value.
     * @param value single value to set for all elements
     */
    void set(T value);

    /**
     * Convert the vector to a T array.
     * <p>The array is independent from vector data, it's elements
     * are copied.</p>
     * @return array containing a copy of vector elements
     */
    T[] toArray();

}
