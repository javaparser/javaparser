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

import org.apache.commons.math3.util.MathArrays;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Exception to be thrown when the a sequence of values is not monotonically
 * increasing or decreasing.
 *
 * @since 2.2 (name changed to "NonMonotonicSequenceException" in 3.0)
 */
public class NonMonotonicSequenceException extends MathIllegalNumberException {
    /** Serializable version Id. */
    private static final long serialVersionUID = 3596849179428944575L;
    /**
     * Direction (positive for increasing, negative for decreasing).
     */
    private final MathArrays.OrderDirection direction;
    /**
     * Whether the sequence must be strictly increasing or decreasing.
     */
    private final boolean strict;
    /**
     * Index of the wrong value.
     */
    private final int index;
    /**
     * Previous value.
     */
    private final Number previous;

    /**
     * Construct the exception.
     * This constructor uses default values assuming that the sequence should
     * have been strictly increasing.
     *
     * @param wrong Value that did not match the requirements.
     * @param previous Previous value in the sequence.
     * @param index Index of the value that did not match the requirements.
     */
    public NonMonotonicSequenceException(Number wrong,
                                         Number previous,
                                         int index) {
        this(wrong, previous, index, MathArrays.OrderDirection.INCREASING, true);
    }

    /**
     * Construct the exception.
     *
     * @param wrong Value that did not match the requirements.
     * @param previous Previous value in the sequence.
     * @param index Index of the value that did not match the requirements.
     * @param direction Strictly positive for a sequence required to be
     * increasing, negative (or zero) for a decreasing sequence.
     * @param strict Whether the sequence must be strictly increasing or
     * decreasing.
     */
    public NonMonotonicSequenceException(Number wrong,
                                         Number previous,
                                         int index,
                                         MathArrays.OrderDirection direction,
                                         boolean strict) {
        super(direction == MathArrays.OrderDirection.INCREASING ?
              (strict ?
               LocalizedFormats.NOT_STRICTLY_INCREASING_SEQUENCE :
               LocalizedFormats.NOT_INCREASING_SEQUENCE) :
              (strict ?
               LocalizedFormats.NOT_STRICTLY_DECREASING_SEQUENCE :
               LocalizedFormats.NOT_DECREASING_SEQUENCE),
              wrong, previous, Integer.valueOf(index), Integer.valueOf(index - 1));

        this.direction = direction;
        this.strict = strict;
        this.index = index;
        this.previous = previous;
    }

    /**
     * @return the order direction.
     **/
    public MathArrays.OrderDirection getDirection() {
        return direction;
    }
    /**
     * @return {@code true} is the sequence should be strictly monotonic.
     **/
    public boolean getStrict() {
        return strict;
    }
    /**
     * Get the index of the wrong value.
     *
     * @return the current index.
     */
    public int getIndex() {
        return index;
    }
    /**
     * @return the previous value.
     */
    public Number getPrevious() {
        return previous;
    }
}
