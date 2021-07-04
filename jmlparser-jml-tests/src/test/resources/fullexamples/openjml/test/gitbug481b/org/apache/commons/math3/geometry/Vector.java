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
package org.apache.commons.math3.geometry;

import java.text.NumberFormat;

import org.apache.commons.math3.exception.MathArithmeticException;

/** This interface represents a generic vector in a vectorial space or a point in an affine space.
 * @param <S> Type of the space.
 * @see Space
 * @see Point
 * @since 3.0
 */
public interface Vector<S extends Space> extends Point<S> {

    /** Get the null vector of the vectorial space or origin point of the affine space.
     * @return null vector of the vectorial space or origin point of the affine space
     */
    Vector<S> getZero();

    /** Get the L<sub>1</sub> norm for the vector.
     * @return L<sub>1</sub> norm for the vector
     */
    double getNorm1();

    /** Get the L<sub>2</sub> norm for the vector.
     * @return Euclidean norm for the vector
     */
    double getNorm();

    /** Get the square of the norm for the vector.
     * @return square of the Euclidean norm for the vector
     */
    double getNormSq();

    /** Get the L<sub>&infin;</sub> norm for the vector.
     * @return L<sub>&infin;</sub> norm for the vector
     */
    double getNormInf();

    /** Add a vector to the instance.
     * @param v vector to add
     * @return a new vector
     */
    Vector<S> add(Vector<S> v);

    /** Add a scaled vector to the instance.
     * @param factor scale factor to apply to v before adding it
     * @param v vector to add
     * @return a new vector
     */
    Vector<S> add(double factor, Vector<S> v);

    /** Subtract a vector from the instance.
     * @param v vector to subtract
     * @return a new vector
     */
    Vector<S> subtract(Vector<S> v);

    /** Subtract a scaled vector from the instance.
     * @param factor scale factor to apply to v before subtracting it
     * @param v vector to subtract
     * @return a new vector
     */
    Vector<S> subtract(double factor, Vector<S> v);

    /** Get the opposite of the instance.
     * @return a new vector which is opposite to the instance
     */
    Vector<S> negate();

    /** Get a normalized vector aligned with the instance.
     * @return a new normalized vector
     * @exception MathArithmeticException if the norm is zero
     */
    Vector<S> normalize() throws MathArithmeticException;

    /** Multiply the instance by a scalar.
     * @param a scalar
     * @return a new vector
     */
    Vector<S> scalarMultiply(double a);

    /**
     * Returns true if any coordinate of this vector is infinite and none are NaN;
     * false otherwise
     * @return  true if any coordinate of this vector is infinite and none are NaN;
     * false otherwise
     */
    boolean isInfinite();

    /** Compute the distance between the instance and another vector according to the L<sub>1</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>q.subtract(p).getNorm1()</code> except that no intermediate
     * vector is built</p>
     * @param v second vector
     * @return the distance between the instance and p according to the L<sub>1</sub> norm
     */
    double distance1(Vector<S> v);

    /** Compute the distance between the instance and another vector according to the L<sub>2</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>q.subtract(p).getNorm()</code> except that no intermediate
     * vector is built</p>
     * @param v second vector
     * @return the distance between the instance and p according to the L<sub>2</sub> norm
     */
    double distance(Vector<S> v);

    /** Compute the distance between the instance and another vector according to the L<sub>&infin;</sub> norm.
     * <p>Calling this method is equivalent to calling:
     * <code>q.subtract(p).getNormInf()</code> except that no intermediate
     * vector is built</p>
     * @param v second vector
     * @return the distance between the instance and p according to the L<sub>&infin;</sub> norm
     */
    double distanceInf(Vector<S> v);

    /** Compute the square of the distance between the instance and another vector.
     * <p>Calling this method is equivalent to calling:
     * <code>q.subtract(p).getNormSq()</code> except that no intermediate
     * vector is built</p>
     * @param v second vector
     * @return the square of the distance between the instance and p
     */
    double distanceSq(Vector<S> v);

    /** Compute the dot-product of the instance and another vector.
     * @param v second vector
     * @return the dot product this.v
     */
    double dotProduct(Vector<S> v);

    /** Get a string representation of this vector.
     * @param format the custom format for components
     * @return a string representation of this vector
     */
    String toString(final NumberFormat format);

}
