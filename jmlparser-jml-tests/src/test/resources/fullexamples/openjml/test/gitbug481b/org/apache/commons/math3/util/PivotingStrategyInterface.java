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

import org.apache.commons.math3.exception.MathIllegalArgumentException;


/**
 * A strategy to pick a pivoting index of an array for doing partitioning.
 * @see MedianOf3PivotingStrategy
 * @see RandomPivotingStrategy
 * @see CentralPivotingStrategy
 * @since 3.4
 */
public interface PivotingStrategyInterface {

    /**
     * Find pivot index of the array so that partition and K<sup>th</sup>
     * element selection can be made
     * @param work data array
     * @param begin index of the first element of the slice
     * @param end index after the last element of the slice
     * @return the index of the pivot element chosen between the
     * first and the last element of the array slice
     * @throws MathIllegalArgumentException when indices exceeds range
     */
    int pivotIndex(double[] work, int begin, int end)
        throws MathIllegalArgumentException;

}
