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
package org.apache.commons.math3.exception;

import org.apache.commons.math3.exception.util.Localizable;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Exception to be thrown when two sets of dimensions differ.
 *
 * @since 3.0
 */
public class MultiDimensionMismatchException extends MathIllegalArgumentException {
    /** Serializable version Id. */
    private static final long serialVersionUID = -8415396756375798143L;

    /** Wrong dimensions. */
    private final Integer[] wrong;
    /** Correct dimensions. */
    private final Integer[] expected;

    /**
     * Construct an exception from the mismatched dimensions.
     *
     * @param wrong Wrong dimensions.
     * @param expected Expected dimensions.
     */
    public MultiDimensionMismatchException(Integer[] wrong,
                                           Integer[] expected) {
        this(LocalizedFormats.DIMENSIONS_MISMATCH, wrong, expected);
    }

    /**
     * Construct an exception from the mismatched dimensions.
     *
     * @param specific Message pattern providing the specific context of
     * the error.
     * @param wrong Wrong dimensions.
     * @param expected Expected dimensions.
     */
    public MultiDimensionMismatchException(Localizable specific,
                                           Integer[] wrong,
                                           Integer[] expected) {
        super(specific, wrong, expected);
        this.wrong = wrong.clone();
        this.expected = expected.clone();
    }

    /**
     * @return an array containing the wrong dimensions.
     */
    public Integer[] getWrongDimensions() {
        return wrong.clone();
    }
    /**
     * @return an array containing the expected dimensions.
     */
    public Integer[] getExpectedDimensions() {
        return expected.clone();
    }

    /**
     * @param index Dimension index.
     * @return the wrong dimension stored at {@code index}.
     */
    public int getWrongDimension(int index) {
        return wrong[index].intValue();
    }
    /**
     * @param index Dimension index.
     * @return the expected dimension stored at {@code index}.
     */
    public int getExpectedDimension(int index) {
        return expected[index].intValue();
    }
}
