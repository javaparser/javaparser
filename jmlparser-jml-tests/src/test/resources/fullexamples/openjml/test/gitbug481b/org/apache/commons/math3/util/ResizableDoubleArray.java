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
package org.apache.commons.math3.util;

import java.io.Serializable;
import java.util.Arrays;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.MathIllegalStateException;
import org.apache.commons.math3.exception.MathInternalError;
import org.apache.commons.math3.exception.NullArgumentException;
import org.apache.commons.math3.exception.NotStrictlyPositiveException;
import org.apache.commons.math3.exception.NumberIsTooSmallException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * <p>
 * A variable length {@link DoubleArray} implementation that automatically
 * handles expanding and contracting its internal storage array as elements
 * are added and removed.
 * </p>
 * <h3>Important note: Usage should not assume that this class is thread-safe
 * even though some of the methods are {@code synchronized}.
 * This qualifier will be dropped in the next major release (4.0).</h3>
 * <p>
 * The internal storage array starts with capacity determined by the
 * {@code initialCapacity} property, which can be set by the constructor.
 * The default initial capacity is 16.  Adding elements using
 * {@link #addElement(double)} appends elements to the end of the array.
 * When there are no open entries at the end of the internal storage array,
 * the array is expanded.  The size of the expanded array depends on the
 * {@code expansionMode} and {@code expansionFactor} properties.
 * The {@code expansionMode} determines whether the size of the array is
 * multiplied by the {@code expansionFactor}
 * ({@link ExpansionMode#MULTIPLICATIVE}) or if the expansion is additive
 * ({@link ExpansionMode#ADDITIVE} -- {@code expansionFactor} storage
 * locations added).
 * The default {@code expansionMode} is {@code MULTIPLICATIVE} and the default
 * {@code expansionFactor} is 2.
 * </p>
 * <p>
 * The {@link #addElementRolling(double)} method adds a new element to the end
 * of the internal storage array and adjusts the "usable window" of the
 * internal array forward by one position (effectively making what was the
 * second element the first, and so on).  Repeated activations of this method
 * (or activation of {@link #discardFrontElements(int)}) will effectively orphan
 * the storage locations at the beginning of the internal storage array.  To
 * reclaim this storage, each time one of these methods is activated, the size
 * of the internal storage array is compared to the number of addressable
 * elements (the {@code numElements} property) and if the difference
 * is too large, the internal array is contracted to size
 * {@code numElements + 1}.  The determination of when the internal
 * storage array is "too large" depends on the {@code expansionMode} and
 * {@code contractionFactor} properties.  If  the {@code expansionMode}
 * is {@code MULTIPLICATIVE}, contraction is triggered when the
 * ratio between storage array length and {@code numElements} exceeds
 * {@code contractionFactor.}  If the {@code expansionMode}
 * is {@code ADDITIVE}, the number of excess storage locations
 * is compared to {@code contractionFactor}.
 * </p>
 * <p>
 * To avoid cycles of expansions and contractions, the
 * {@code expansionFactor} must not exceed the {@code contractionFactor}.
 * Constructors and mutators for both of these properties enforce this
 * requirement, throwing a {@code MathIllegalArgumentException} if it is
 * violated.
 * </p>
 */
public class ResizableDoubleArray implements DoubleArray, Serializable {
    /** Additive expansion mode.
     * @deprecated As of 3.1. Please use {@link ExpansionMode#ADDITIVE} instead.
     */
    @Deprecated
    public static final int ADDITIVE_MODE = 1;
    /** Multiplicative expansion mode.
     * @deprecated As of 3.1. Please use {@link ExpansionMode#MULTIPLICATIVE} instead.
     */
    @Deprecated
    public static final int MULTIPLICATIVE_MODE = 0;
    /** Serializable version identifier. */
    private static final long serialVersionUID = -3485529955529426875L;

    /** Default value for initial capacity. */
    private static final int DEFAULT_INITIAL_CAPACITY = 16;
    /** Default value for array size modifier. */
    private static final double DEFAULT_EXPANSION_FACTOR = 2.0;
    /**
     * Default value for the difference between {@link #contractionCriterion}
     * and {@link #expansionFactor}.
     */
    private static final double DEFAULT_CONTRACTION_DELTA = 0.5;

    /**
     * The contraction criteria determines when the internal array will be
     * contracted to fit the number of elements contained in the element
     *  array + 1.
     */
    private double contractionCriterion = 2.5;

    /**
     * The expansion factor of the array.  When the array needs to be expanded,
     * the new array size will be
     * {@code internalArray.length * expansionFactor}
     * if {@code expansionMode} is set to MULTIPLICATIVE_MODE, or
     * {@code internalArray.length + expansionFactor} if
     * {@code expansionMode} is set to ADDITIVE_MODE.
     */
    private double expansionFactor = 2.0;

    /**
     * Determines whether array expansion by {@code expansionFactor}
     * is additive or multiplicative.
     */
    private ExpansionMode expansionMode = ExpansionMode.MULTIPLICATIVE;

    /**
     * The internal storage array.
     */
    private double[] internalArray;

    /**
     * The number of addressable elements in the array.  Note that this
     * has nothing to do with the length of the internal storage array.
     */
    private int numElements = 0;

    /**
     * The position of the first addressable element in the internal storage
     * array.  The addressable elements in the array are
     * {@code internalArray[startIndex],...,internalArray[startIndex + numElements - 1]}.
     */
    private int startIndex = 0;

    /**
     * Specification of expansion algorithm.
     * @since 3.1
     */
    public enum ExpansionMode {
        /** Multiplicative expansion mode. */
        MULTIPLICATIVE,
        /** Additive expansion mode. */
        ADDITIVE
    }

    /**
     * Creates an instance with default properties.
     * <ul>
     *  <li>{@code initialCapacity = 16}</li>
     *  <li>{@code expansionMode = MULTIPLICATIVE}</li>
     *  <li>{@code expansionFactor = 2.0}</li>
     *  <li>{@code contractionCriterion = 2.5}</li>
     * </ul>
     */
    public ResizableDoubleArray() {
        this(DEFAULT_INITIAL_CAPACITY);
    }

    /**
     * Creates an instance with the specified initial capacity.
     * Other properties take default values:
     * <ul>
     *  <li>{@code expansionMode = MULTIPLICATIVE}</li>
     *  <li>{@code expansionFactor = 2.0}</li>
     *  <li>{@code contractionCriterion = 2.5}</li>
     * </ul>
     * @param initialCapacity Initial size of the internal storage array.
     * @throws MathIllegalArgumentException if {@code initialCapacity <= 0}.
     */
    public ResizableDoubleArray(int initialCapacity)
        throws MathIllegalArgumentException {
        this(initialCapacity, DEFAULT_EXPANSION_FACTOR);
    }

    /**
     * Creates an instance from an existing {@code double[]} with the
     * initial capacity and numElements corresponding to the size of
     * the supplied {@code double[]} array.
     * If the supplied array is null, a new empty array with the default
     * initial capacity will be created.
     * The input array is copied, not referenced.
     * Other properties take default values:
     * <ul>
     *  <li>{@code initialCapacity = 16}</li>
     *  <li>{@code expansionMode = MULTIPLICATIVE}</li>
     *  <li>{@code expansionFactor = 2.0}</li>
     *  <li>{@code contractionCriterion = 2.5}</li>
     * </ul>
     *
     * @param initialArray initial array
     * @since 2.2
     */
    public ResizableDoubleArray(double[] initialArray) {
        this(DEFAULT_INITIAL_CAPACITY,
             DEFAULT_EXPANSION_FACTOR,
             DEFAULT_CONTRACTION_DELTA + DEFAULT_EXPANSION_FACTOR,
             ExpansionMode.MULTIPLICATIVE,
             initialArray);
    }

    /**
     * Creates an instance with the specified initial capacity
     * and expansion factor.
     * The remaining properties take default values:
     * <ul>
     *  <li>{@code expansionMode = MULTIPLICATIVE}</li>
     *  <li>{@code contractionCriterion = 0.5 + expansionFactor}</li>
     * </ul>
     * <br/>
     * Throws IllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     *  <li>{@code initialCapacity > 0}</li>
     *  <li>{@code expansionFactor > 1}</li>
     * </ul>
     *
     * @param initialCapacity Initial size of the internal storage array.
     * @param expansionFactor The array will be expanded based on this
     * parameter.
     * @throws MathIllegalArgumentException if parameters are not valid.
     * @deprecated As of 3.1. Please use
     * {@link #ResizableDoubleArray(int,double)} instead.
     */
    @Deprecated
    public ResizableDoubleArray(int initialCapacity,
                                float expansionFactor)
        throws MathIllegalArgumentException {
        this(initialCapacity,
             (double) expansionFactor);
    }

    /**
     * Creates an instance with the specified initial capacity
     * and expansion factor.
     * The remaining properties take default values:
     * <ul>
     *  <li>{@code expansionMode = MULTIPLICATIVE}</li>
     *  <li>{@code contractionCriterion = 0.5 + expansionFactor}</li>
     * </ul>
     * <br/>
     * Throws IllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     *  <li>{@code initialCapacity > 0}</li>
     *  <li>{@code expansionFactor > 1}</li>
     * </ul>
     *
     * @param initialCapacity Initial size of the internal storage array.
     * @param expansionFactor The array will be expanded based on this
     * parameter.
     * @throws MathIllegalArgumentException if parameters are not valid.
     * @since 3.1
     */
    public ResizableDoubleArray(int initialCapacity,
                                double expansionFactor)
        throws MathIllegalArgumentException {
        this(initialCapacity,
             expansionFactor,
             DEFAULT_CONTRACTION_DELTA + expansionFactor);
    }

    /**
     * Creates an instance with the specified initialCapacity,
     * expansionFactor, and contractionCriterion.
     * The expansion mode will default to {@code MULTIPLICATIVE}.
     * <br/>
     * Throws IllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     *  <li>{@code initialCapacity > 0}</li>
     *  <li>{@code expansionFactor > 1}</li>
     *  <li>{@code contractionCriterion >= expansionFactor}</li>
     * </ul>
     *
     * @param initialCapacity Initial size of the internal storage array..
     * @param expansionFactor The array will be expanded based on this
     * parameter.
     * @param contractionCriteria Contraction criteria.
     * @throws MathIllegalArgumentException if parameters are not valid.
     * @deprecated As of 3.1. Please use
     * {@link #ResizableDoubleArray(int,double,double)} instead.
     */
    @Deprecated
    public ResizableDoubleArray(int initialCapacity,
                                float expansionFactor,
                                float contractionCriteria)
        throws MathIllegalArgumentException {
        this(initialCapacity,
             (double) expansionFactor,
             (double) contractionCriteria);
    }

    /**
     * Creates an instance with the specified initial capacity,
     * expansion factor, and contraction criteria.
     * The expansion mode will default to {@code MULTIPLICATIVE}.
     * <br/>
     * Throws IllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     *  <li>{@code initialCapacity > 0}</li>
     *  <li>{@code expansionFactor > 1}</li>
     *  <li>{@code contractionCriterion >= expansionFactor}</li>
     * </ul>
     *
     * @param initialCapacity Initial size of the internal storage array..
     * @param expansionFactor The array will be expanded based on this
     * parameter.
     * @param contractionCriterion Contraction criterion.
     * @throws MathIllegalArgumentException if the parameters are not valid.
     * @since 3.1
     */
    public ResizableDoubleArray(int initialCapacity,
                                double expansionFactor,
                                double contractionCriterion)
        throws MathIllegalArgumentException {
        this(initialCapacity,
             expansionFactor,
             contractionCriterion,
             ExpansionMode.MULTIPLICATIVE,
             null);
    }

    /**
     * <p>
     * Create a ResizableArray with the specified properties.</p>
     * <p>
     * Throws IllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     * <li><code>initialCapacity > 0</code></li>
     * <li><code>expansionFactor > 1</code></li>
     * <li><code>contractionFactor >= expansionFactor</code></li>
     * <li><code>expansionMode in {MULTIPLICATIVE_MODE, ADDITIVE_MODE}</code>
     * </li>
     * </ul></p>
     *
     * @param initialCapacity the initial size of the internal storage array
     * @param expansionFactor the array will be expanded based on this
     *                        parameter
     * @param contractionCriteria the contraction Criteria
     * @param expansionMode  the expansion mode
     * @throws MathIllegalArgumentException if parameters are not valid
     * @deprecated As of 3.1. Please use
     * {@link #ResizableDoubleArray(int,double,double,ExpansionMode,double[])}
     * instead.
     */
    @Deprecated
    public ResizableDoubleArray(int initialCapacity, float expansionFactor,
            float contractionCriteria, int expansionMode) throws MathIllegalArgumentException {
        this(initialCapacity,
             expansionFactor,
             contractionCriteria,
             expansionMode == ADDITIVE_MODE ?
             ExpansionMode.ADDITIVE :
             ExpansionMode.MULTIPLICATIVE,
             null);
        // XXX Just ot retain the expected failure in a unit test.
        // With the new "enum", that test will become obsolete.
        setExpansionMode(expansionMode);
    }

    /**
     * Creates an instance with the specified properties.
     * <br/>
     * Throws MathIllegalArgumentException if the following conditions are
     * not met:
     * <ul>
     *  <li>{@code initialCapacity > 0}</li>
     *  <li>{@code expansionFactor > 1}</li>
     *  <li>{@code contractionCriterion >= expansionFactor}</li>
     * </ul>
     *
     * @param initialCapacity Initial size of the internal storage array.
     * @param expansionFactor The array will be expanded based on this
     * parameter.
     * @param contractionCriterion Contraction criteria.
     * @param expansionMode Expansion mode.
     * @param data Initial contents of the array.
     * @throws MathIllegalArgumentException if the parameters are not valid.
     */
    public ResizableDoubleArray(int initialCapacity,
                                double expansionFactor,
                                double contractionCriterion,
                                ExpansionMode expansionMode,
                                double ... data)
        throws MathIllegalArgumentException {
        if (initialCapacity <= 0) {
            throw new NotStrictlyPositiveException(LocalizedFormats.INITIAL_CAPACITY_NOT_POSITIVE,
                                                   initialCapacity);
        }
        checkContractExpand(contractionCriterion, expansionFactor);

        this.expansionFactor = expansionFactor;
        this.contractionCriterion = contractionCriterion;
        this.expansionMode = expansionMode;
        internalArray = new double[initialCapacity];
        numElements = 0;
        startIndex = 0;

        if (data != null && data.length > 0) {
            addElements(data);
        }
    }

    /**
     * Copy constructor.  Creates a new ResizableDoubleArray that is a deep,
     * fresh copy of the original. Needs to acquire synchronization lock
     * on original.  Original may not be null; otherwise a {@link NullArgumentException}
     * is thrown.
     *
     * @param original array to copy
     * @exception NullArgumentException if original is null
     * @since 2.0
     */
    public ResizableDoubleArray(ResizableDoubleArray original)
        throws NullArgumentException {
        MathUtils.checkNotNull(original);
        copy(original, this);
    }

    /**
     * Adds an element to the end of this expandable array.
     *
     * @param value Value to be added to end of array.
     */
    public synchronized void addElement(double value) {
        if (internalArray.length <= startIndex + numElements) {
            expand();
        }
        internalArray[startIndex + numElements++] = value;
    }

    /**
     * Adds several element to the end of this expandable array.
     *
     * @param values Values to be added to end of array.
     * @since 2.2
     */
    public synchronized void addElements(double[] values) {
        final double[] tempArray = new double[numElements + values.length + 1];
        System.arraycopy(internalArray, startIndex, tempArray, 0, numElements);
        System.arraycopy(values, 0, tempArray, numElements, values.length);
        internalArray = tempArray;
        startIndex = 0;
        numElements += values.length;
    }

    /**
     * <p>
     * Adds an element to the end of the array and removes the first
     * element in the array.  Returns the discarded first element.
     * The effect is similar to a push operation in a FIFO queue.
     * </p>
     * <p>
     * Example: If the array contains the elements 1, 2, 3, 4 (in that order)
     * and addElementRolling(5) is invoked, the result is an array containing
     * the entries 2, 3, 4, 5 and the value returned is 1.
     * </p>
     *
     * @param value Value to be added to the array.
     * @return the value which has been discarded or "pushed" out of the array
     * by this rolling insert.
     */
    public synchronized double addElementRolling(double value) {
        double discarded = internalArray[startIndex];

        if ((startIndex + (numElements + 1)) > internalArray.length) {
            expand();
        }
        // Increment the start index
        startIndex += 1;

        // Add the new value
        internalArray[startIndex + (numElements - 1)] = value;

        // Check the contraction criterion.
        if (shouldContract()) {
            contract();
        }
        return discarded;
    }

    /**
     * Substitutes <code>value</code> for the most recently added value.
     * Returns the value that has been replaced. If the array is empty (i.e.
     * if {@link #numElements} is zero), an IllegalStateException is thrown.
     *
     * @param value New value to substitute for the most recently added value
     * @return the value that has been replaced in the array.
     * @throws MathIllegalStateException if the array is empty
     * @since 2.0
     */
    public synchronized double substituteMostRecentElement(double value)
        throws MathIllegalStateException {
        if (numElements < 1) {
            throw new MathIllegalStateException(
                    LocalizedFormats.CANNOT_SUBSTITUTE_ELEMENT_FROM_EMPTY_ARRAY);
        }

        final int substIndex = startIndex + (numElements - 1);
        final double discarded = internalArray[substIndex];

        internalArray[substIndex] = value;

        return discarded;
    }

    /**
     * Checks the expansion factor and the contraction criterion and throws an
     * IllegalArgumentException if the contractionCriteria is less than the
     * expansionCriteria
     *
     * @param expansion factor to be checked
     * @param contraction criteria to be checked
     * @throws MathIllegalArgumentException if the contractionCriteria is less than
     * the expansionCriteria.
     * @deprecated As of 3.1. Please use
     * {@link #checkContractExpand(double,double)} instead.
     */
    @Deprecated
    protected void checkContractExpand(float contraction, float expansion)
        throws MathIllegalArgumentException {
        checkContractExpand((double) contraction,
                            (double) expansion);
    }

    /**
     * Checks the expansion factor and the contraction criterion and raises
     * an exception if the contraction criterion is smaller than the
     * expansion criterion.
     *
     * @param contraction Criterion to be checked.
     * @param expansion Factor to be checked.
     * @throws NumberIsTooSmallException if {@code contraction < expansion}.
     * @throws NumberIsTooSmallException if {@code contraction <= 1}.
     * @throws NumberIsTooSmallException if {@code expansion <= 1 }.
     * @since 3.1
     */
    protected void checkContractExpand(double contraction,
                                       double expansion)
        throws NumberIsTooSmallException {
        if (contraction < expansion) {
            final NumberIsTooSmallException e = new NumberIsTooSmallException(contraction, 1, true);
            e.getContext().addMessage(LocalizedFormats.CONTRACTION_CRITERIA_SMALLER_THAN_EXPANSION_FACTOR,
                                      contraction, expansion);
            throw e;
        }

        if (contraction <= 1) {
            final NumberIsTooSmallException e = new NumberIsTooSmallException(contraction, 1, false);
            e.getContext().addMessage(LocalizedFormats.CONTRACTION_CRITERIA_SMALLER_THAN_ONE,
                                      contraction);
            throw e;
        }

        if (expansion <= 1) {
            final NumberIsTooSmallException e = new NumberIsTooSmallException(contraction, 1, false);
            e.getContext().addMessage(LocalizedFormats.EXPANSION_FACTOR_SMALLER_THAN_ONE,
                                      expansion);
            throw e;
        }
    }

    /**
     * Clear the array contents, resetting the number of elements to zero.
     */
    public synchronized void clear() {
        numElements = 0;
        startIndex = 0;
    }

    /**
     * Contracts the storage array to the (size of the element set) + 1 - to
     * avoid a zero length array. This function also resets the startIndex to
     * zero.
     */
    public synchronized void contract() {
        final double[] tempArray = new double[numElements + 1];

        // Copy and swap - copy only the element array from the src array.
        System.arraycopy(internalArray, startIndex, tempArray, 0, numElements);
        internalArray = tempArray;

        // Reset the start index to zero
        startIndex = 0;
    }

    /**
     * Discards the <code>i</code> initial elements of the array.  For example,
     * if the array contains the elements 1,2,3,4, invoking
     * <code>discardFrontElements(2)</code> will cause the first two elements
     * to be discarded, leaving 3,4 in the array.  Throws illegalArgumentException
     * if i exceeds numElements.
     *
     * @param i  the number of elements to discard from the front of the array
     * @throws MathIllegalArgumentException if i is greater than numElements.
     * @since 2.0
     */
    public synchronized void discardFrontElements(int i)
        throws MathIllegalArgumentException {
        discardExtremeElements(i,true);
    }

    /**
     * Discards the <code>i</code> last elements of the array.  For example,
     * if the array contains the elements 1,2,3,4, invoking
     * <code>discardMostRecentElements(2)</code> will cause the last two elements
     * to be discarded, leaving 1,2 in the array.  Throws illegalArgumentException
     * if i exceeds numElements.
     *
     * @param i  the number of elements to discard from the end of the array
     * @throws MathIllegalArgumentException if i is greater than numElements.
     * @since 2.0
     */
    public synchronized void discardMostRecentElements(int i)
        throws MathIllegalArgumentException {
        discardExtremeElements(i,false);
    }

    /**
     * Discards the <code>i</code> first or last elements of the array,
     * depending on the value of <code>front</code>.
     * For example, if the array contains the elements 1,2,3,4, invoking
     * <code>discardExtremeElements(2,false)</code> will cause the last two elements
     * to be discarded, leaving 1,2 in the array.
     * For example, if the array contains the elements 1,2,3,4, invoking
     * <code>discardExtremeElements(2,true)</code> will cause the first two elements
     * to be discarded, leaving 3,4 in the array.
     * Throws illegalArgumentException
     * if i exceeds numElements.
     *
     * @param i  the number of elements to discard from the front/end of the array
     * @param front true if elements are to be discarded from the front
     * of the array, false if elements are to be discarded from the end
     * of the array
     * @throws MathIllegalArgumentException if i is greater than numElements.
     * @since 2.0
     */
    private synchronized void discardExtremeElements(int i,
                                                     boolean front)
        throws MathIllegalArgumentException {
        if (i > numElements) {
            throw new MathIllegalArgumentException(
                    LocalizedFormats.TOO_MANY_ELEMENTS_TO_DISCARD_FROM_ARRAY,
                    i, numElements);
       } else if (i < 0) {
           throw new MathIllegalArgumentException(
                   LocalizedFormats.CANNOT_DISCARD_NEGATIVE_NUMBER_OF_ELEMENTS,
                   i);
        } else {
            // "Subtract" this number of discarded from numElements
            numElements -= i;
            if (front) {
                startIndex += i;
            }
        }
        if (shouldContract()) {
            contract();
        }
    }

    /**
     * Expands the internal storage array using the expansion factor.
     * <p>
     * if <code>expansionMode</code> is set to MULTIPLICATIVE_MODE,
     * the new array size will be <code>internalArray.length * expansionFactor.</code>
     * If <code>expansionMode</code> is set to ADDITIVE_MODE,  the length
     * after expansion will be <code>internalArray.length + expansionFactor</code>
     * </p>
     */
    protected synchronized void expand() {
        // notice the use of FastMath.ceil(), this guarantees that we will always
        // have an array of at least currentSize + 1.   Assume that the
        // current initial capacity is 1 and the expansion factor
        // is 1.000000000000000001.  The newly calculated size will be
        // rounded up to 2 after the multiplication is performed.
        int newSize = 0;
        if (expansionMode == ExpansionMode.MULTIPLICATIVE) {
            newSize = (int) FastMath.ceil(internalArray.length * expansionFactor);
        } else {
            newSize = (int) (internalArray.length + FastMath.round(expansionFactor));
        }
        final double[] tempArray = new double[newSize];

        // Copy and swap
        System.arraycopy(internalArray, 0, tempArray, 0, internalArray.length);
        internalArray = tempArray;
    }

    /**
     * Expands the internal storage array to the specified size.
     *
     * @param size Size of the new internal storage array.
     */
    private synchronized void expandTo(int size) {
        final double[] tempArray = new double[size];
        // Copy and swap
        System.arraycopy(internalArray, 0, tempArray, 0, internalArray.length);
        internalArray = tempArray;
    }

    /**
     * The contraction criteria defines when the internal array will contract
     * to store only the number of elements in the element array.
     * If  the <code>expansionMode</code> is <code>MULTIPLICATIVE_MODE</code>,
     * contraction is triggered when the ratio between storage array length
     * and <code>numElements</code> exceeds <code>contractionFactor</code>.
     * If the <code>expansionMode</code> is <code>ADDITIVE_MODE</code>, the
     * number of excess storage locations is compared to
     * <code>contractionFactor.</code>
     *
     * @return the contraction criteria used to reclaim memory.
     * @deprecated As of 3.1. Please use {@link #getContractionCriterion()}
     * instead.
     */
    @Deprecated
    public float getContractionCriteria() {
        return (float) getContractionCriterion();
    }

    /**
     * The contraction criterion defines when the internal array will contract
     * to store only the number of elements in the element array.
     * If  the <code>expansionMode</code> is <code>MULTIPLICATIVE_MODE</code>,
     * contraction is triggered when the ratio between storage array length
     * and <code>numElements</code> exceeds <code>contractionFactor</code>.
     * If the <code>expansionMode</code> is <code>ADDITIVE_MODE</code>, the
     * number of excess storage locations is compared to
     * <code>contractionFactor.</code>
     *
     * @return the contraction criterion used to reclaim memory.
     * @since 3.1
     */
    public double getContractionCriterion() {
        return contractionCriterion;
    }

    /**
     * Returns the element at the specified index
     *
     * @param index index to fetch a value from
     * @return value stored at the specified index
     * @throws ArrayIndexOutOfBoundsException if <code>index</code> is less than
     * zero or is greater than <code>getNumElements() - 1</code>.
     */
    public synchronized double getElement(int index) {
        if (index >= numElements) {
            throw new ArrayIndexOutOfBoundsException(index);
        } else if (index >= 0) {
            return internalArray[startIndex + index];
        } else {
            throw new ArrayIndexOutOfBoundsException(index);
        }
    }

     /**
     * Returns a double array containing the elements of this
     * <code>ResizableArray</code>.  This method returns a copy, not a
     * reference to the underlying array, so that changes made to the returned
     *  array have no effect on this <code>ResizableArray.</code>
     * @return the double array.
     */
    public synchronized double[] getElements() {
        final double[] elementArray = new double[numElements];
        System.arraycopy(internalArray, startIndex, elementArray, 0, numElements);
        return elementArray;
    }

    /**
     * The expansion factor controls the size of a new array when an array
     * needs to be expanded.  The <code>expansionMode</code>
     * determines whether the size of the array is multiplied by the
     * <code>expansionFactor</code> (MULTIPLICATIVE_MODE) or if
     * the expansion is additive (ADDITIVE_MODE -- <code>expansionFactor</code>
     * storage locations added).  The default <code>expansionMode</code> is
     * MULTIPLICATIVE_MODE and the default <code>expansionFactor</code>
     * is 2.0.
     *
     * @return the expansion factor of this expandable double array
     * @deprecated As of 3.1. Return type will be changed to "double" in 4.0.
     */
    @Deprecated
    public float getExpansionFactor() {
        return (float) expansionFactor;
    }

    /**
     * The expansion mode determines whether the internal storage
     * array grows additively or multiplicatively when it is expanded.
     *
     * @return the expansion mode.
     * @deprecated As of 3.1. Return value to be changed to
     * {@link ExpansionMode} in 4.0.
     */
    @Deprecated
    public int getExpansionMode() {
        synchronized (this) {
            switch (expansionMode) {
                case MULTIPLICATIVE:
                    return MULTIPLICATIVE_MODE;
                case ADDITIVE:
                    return ADDITIVE_MODE;
                default:
                    throw new MathInternalError(); // Should never happen.
            }
        }
    }

    /**
     * Notice the package scope on this method.   This method is simply here
     * for the JUnit test, it allows us check if the expansion is working
     * properly after a number of expansions.  This is not meant to be a part
     * of the public interface of this class.
     *
     * @return the length of the internal storage array.
     * @deprecated As of 3.1. Please use {@link #getCapacity()} instead.
     */
    @Deprecated
    synchronized int getInternalLength() {
        return internalArray.length;
    }

    /**
     * Gets the currently allocated size of the internal data structure used
     * for storing elements.
     * This is not to be confused with {@link #getNumElements() the number of
     * elements actually stored}.
     *
     * @return the length of the internal array.
     * @since 3.1
     */
    public int getCapacity() {
        return internalArray.length;
    }

    /**
     * Returns the number of elements currently in the array.  Please note
     * that this is different from the length of the internal storage array.
     *
     * @return the number of elements.
     */
    public synchronized int getNumElements() {
        return numElements;
    }

    /**
     * Returns the internal storage array.  Note that this method returns
     * a reference to the internal storage array, not a copy, and to correctly
     * address elements of the array, the <code>startIndex</code> is
     * required (available via the {@link #start} method).  This method should
     * only be used in cases where copying the internal array is not practical.
     * The {@link #getElements} method should be used in all other cases.
     *
     *
     * @return the internal storage array used by this object
     * @since 2.0
     * @deprecated As of 3.1.
     */
    @Deprecated
    public synchronized double[] getInternalValues() {
        return internalArray;
    }

    /**
     * Provides <em>direct</em> access to the internal storage array.
     * Please note that this method returns a reference to this object's
     * storage array, not a copy.
     * <br/>
     * To correctly address elements of the array, the "start index" is
     * required (available via the {@link #getStartIndex() getStartIndex}
     * method.
     * <br/>
     * This method should only be used to avoid copying the internal array.
     * The returned value <em>must</em> be used for reading only; other
     * uses could lead to this object becoming inconsistent.
     * <br/>
     * The {@link #getElements} method has no such limitation since it
     * returns a copy of this array's addressable elements.
     *
     * @return the internal storage array used by this object.
     * @since 3.1
     */
    protected double[] getArrayRef() {
        return internalArray;
    }

    /**
     * Returns the "start index" of the internal array.
     * This index is the position of the first addressable element in the
     * internal storage array.
     * The addressable elements in the array are at indices contained in
     * the interval [{@link #getStartIndex()},
     *               {@link #getStartIndex()} + {@link #getNumElements()} - 1].
     *
     * @return the start index.
     * @since 3.1
     */
    protected int getStartIndex() {
        return startIndex;
    }

    /**
     * Sets the contraction criteria.
     *
     * @param contractionCriteria contraction criteria
     * @throws MathIllegalArgumentException if the contractionCriteria is less than
     *         the expansionCriteria.
     * @deprecated As of 3.1 (to be removed in 4.0 as field will become "final").
     */
    @Deprecated
    public void setContractionCriteria(float contractionCriteria)
        throws MathIllegalArgumentException {
        checkContractExpand(contractionCriteria, getExpansionFactor());
        synchronized(this) {
            this.contractionCriterion = contractionCriteria;
        }
    }

    /**
     * Performs an operation on the addressable elements of the array.
     *
     * @param f Function to be applied on this array.
     * @return the result.
     * @since 3.1
     */
    public double compute(MathArrays.Function f) {
        final double[] array;
        final int start;
        final int num;
        synchronized(this) {
            array = internalArray;
            start = startIndex;
            num   = numElements;
        }
        return f.evaluate(array, start, num);
    }

    /**
     * Sets the element at the specified index.  If the specified index is greater than
     * <code>getNumElements() - 1</code>, the <code>numElements</code> property
     * is increased to <code>index +1</code> and additional storage is allocated
     * (if necessary) for the new element and all  (uninitialized) elements
     * between the new element and the previous end of the array).
     *
     * @param index index to store a value in
     * @param value value to store at the specified index
     * @throws ArrayIndexOutOfBoundsException if {@code index < 0}.
     */
    public synchronized void setElement(int index, double value) {
        if (index < 0) {
            throw new ArrayIndexOutOfBoundsException(index);
        }
        if (index + 1 > numElements) {
            numElements = index + 1;
        }
        if ((startIndex + index) >= internalArray.length) {
            expandTo(startIndex + (index + 1));
        }
        internalArray[startIndex + index] = value;
    }

    /**
     * Sets the expansionFactor.  Throws IllegalArgumentException if the
     * the following conditions are not met:
     * <ul>
     * <li><code>expansionFactor > 1</code></li>
     * <li><code>contractionFactor >= expansionFactor</code></li>
     * </ul>
     * @param expansionFactor the new expansion factor value.
     * @throws MathIllegalArgumentException if expansionFactor is <= 1 or greater
     * than contractionFactor
     * @deprecated As of 3.1 (to be removed in 4.0 as field will become "final").
     */
    @Deprecated
    public void setExpansionFactor(float expansionFactor) throws MathIllegalArgumentException {
        checkContractExpand(getContractionCriterion(), expansionFactor);
        // The check above verifies that the expansion factor is > 1.0;
        synchronized(this) {
            this.expansionFactor = expansionFactor;
        }
    }

    /**
     * Sets the <code>expansionMode</code>. The specified value must be one of
     * ADDITIVE_MODE, MULTIPLICATIVE_MODE.
     *
     * @param expansionMode The expansionMode to set.
     * @throws MathIllegalArgumentException if the specified mode value is not valid.
     * @deprecated As of 3.1. Please use {@link #setExpansionMode(ExpansionMode)} instead.
     */
    @Deprecated
    public void setExpansionMode(int expansionMode)
        throws MathIllegalArgumentException {
        if (expansionMode != MULTIPLICATIVE_MODE &&
            expansionMode != ADDITIVE_MODE) {
            throw new MathIllegalArgumentException(LocalizedFormats.UNSUPPORTED_EXPANSION_MODE, expansionMode,
                                                   MULTIPLICATIVE_MODE, "MULTIPLICATIVE_MODE",
                                                   ADDITIVE_MODE, "ADDITIVE_MODE");
        }
        synchronized(this) {
            if (expansionMode == MULTIPLICATIVE_MODE) {
                setExpansionMode(ExpansionMode.MULTIPLICATIVE);
            } else if (expansionMode == ADDITIVE_MODE) {
                setExpansionMode(ExpansionMode.ADDITIVE);
            }
        }
    }

    /**
     * Sets the {@link ExpansionMode expansion mode}.
     *
     * @param expansionMode Expansion mode to use for resizing the array.
     * @deprecated As of 3.1 (to be removed in 4.0 as field will become "final").
     */
    @Deprecated
    public void setExpansionMode(ExpansionMode expansionMode) {
        synchronized(this) {
            this.expansionMode = expansionMode;
        }
    }

    /**
     * Sets the initial capacity.  Should only be invoked by constructors.
     *
     * @param initialCapacity of the array
     * @throws MathIllegalArgumentException if <code>initialCapacity</code> is not
     * positive.
     * @deprecated As of 3.1, this is a no-op.
     */
    @Deprecated
    protected void setInitialCapacity(int initialCapacity)
        throws MathIllegalArgumentException {
        // Body removed in 3.1.
    }

    /**
     * This function allows you to control the number of elements contained
     * in this array, and can be used to "throw out" the last n values in an
     * array. This function will also expand the internal array as needed.
     *
     * @param i a new number of elements
     * @throws MathIllegalArgumentException if <code>i</code> is negative.
     */
    public synchronized void setNumElements(int i)
        throws MathIllegalArgumentException {
        // If index is negative thrown an error.
        if (i < 0) {
            throw new MathIllegalArgumentException(
                    LocalizedFormats.INDEX_NOT_POSITIVE,
                    i);
        }

        // Test the new num elements, check to see if the array needs to be
        // expanded to accommodate this new number of elements.
        final int newSize = startIndex + i;
        if (newSize > internalArray.length) {
            expandTo(newSize);
        }

        // Set the new number of elements to new value.
        numElements = i;
    }

    /**
     * Returns true if the internal storage array has too many unused
     * storage positions.
     *
     * @return true if array satisfies the contraction criteria
     */
    private synchronized boolean shouldContract() {
        if (expansionMode == ExpansionMode.MULTIPLICATIVE) {
            return (internalArray.length / ((float) numElements)) > contractionCriterion;
        } else {
            return (internalArray.length - numElements) > contractionCriterion;
        }
    }

    /**
     * Returns the starting index of the internal array.  The starting index is
     * the position of the first addressable element in the internal storage
     * array.  The addressable elements in the array are <code>
     * internalArray[startIndex],...,internalArray[startIndex + numElements -1]
     * </code>
     *
     * @return the starting index.
     * @deprecated As of 3.1.
     */
    @Deprecated
    public synchronized int start() {
        return startIndex;
    }

    /**
     * <p>Copies source to dest, copying the underlying data, so dest is
     * a new, independent copy of source.  Does not contract before
     * the copy.</p>
     *
     * <p>Obtains synchronization locks on both source and dest
     * (in that order) before performing the copy.</p>
     *
     * <p>Neither source nor dest may be null; otherwise a {@link NullArgumentException}
     * is thrown</p>
     *
     * @param source ResizableDoubleArray to copy
     * @param dest ResizableArray to replace with a copy of the source array
     * @exception NullArgumentException if either source or dest is null
     * @since 2.0
     *
     */
    public static void copy(ResizableDoubleArray source,
                            ResizableDoubleArray dest)
        throws NullArgumentException {
        MathUtils.checkNotNull(source);
        MathUtils.checkNotNull(dest);
        synchronized(source) {
           synchronized(dest) {
               dest.contractionCriterion = source.contractionCriterion;
               dest.expansionFactor = source.expansionFactor;
               dest.expansionMode = source.expansionMode;
               dest.internalArray = new double[source.internalArray.length];
               System.arraycopy(source.internalArray, 0, dest.internalArray,
                       0, dest.internalArray.length);
               dest.numElements = source.numElements;
               dest.startIndex = source.startIndex;
           }
       }
    }

    /**
     * Returns a copy of the ResizableDoubleArray.  Does not contract before
     * the copy, so the returned object is an exact copy of this.
     *
     * @return a new ResizableDoubleArray with the same data and configuration
     * properties as this
     * @since 2.0
     */
    public synchronized ResizableDoubleArray copy() {
        final ResizableDoubleArray result = new ResizableDoubleArray();
        copy(this, result);
        return result;
    }

    /**
     * Returns true iff object is a ResizableDoubleArray with the same properties
     * as this and an identical internal storage array.
     *
     * @param object object to be compared for equality with this
     * @return true iff object is a ResizableDoubleArray with the same data and
     * properties as this
     * @since 2.0
     */
    @Override
    public boolean equals(Object object) {
        if (object == this ) {
            return true;
        }
        if (object instanceof ResizableDoubleArray == false) {
            return false;
        }
        synchronized(this) {
            synchronized(object) {
                boolean result = true;
                final ResizableDoubleArray other = (ResizableDoubleArray) object;
                result = result && (other.contractionCriterion == contractionCriterion);
                result = result && (other.expansionFactor == expansionFactor);
                result = result && (other.expansionMode == expansionMode);
                result = result && (other.numElements == numElements);
                result = result && (other.startIndex == startIndex);
                if (!result) {
                    return false;
                } else {
                    return Arrays.equals(internalArray, other.internalArray);
                }
            }
        }
    }

    /**
     * Returns a hash code consistent with equals.
     *
     * @return the hash code representing this {@code ResizableDoubleArray}.
     * @since 2.0
     */
    @Override
    public synchronized int hashCode() {
        final int[] hashData = new int[6];
        hashData[0] = Double.valueOf(expansionFactor).hashCode();
        hashData[1] = Double.valueOf(contractionCriterion).hashCode();
        hashData[2] = expansionMode.hashCode();
        hashData[3] = Arrays.hashCode(internalArray);
        hashData[4] = numElements;
        hashData[5] = startIndex;
        return Arrays.hashCode(hashData);
    }

}
