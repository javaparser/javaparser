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

package org.apache.commons.math3.stat.ranking;

/**
 * Interface representing a rank transformation.
 *
 * @since 2.0
 */
public interface RankingAlgorithm {
    /**
     * <p>Performs a rank transformation on the input data, returning an array
     * of ranks.</p>
     *
     * <p>Ranks should be 1-based - that is, the smallest value
     * returned in an array of ranks should be greater than or equal to one,
     * rather than 0. Ranks should in general take integer values, though
     * implementations may return averages or other floating point values
     * to resolve ties in the input data.</p>
     *
     * @param data array of data to be ranked
     * @return an array of ranks corresponding to the elements of the input array
     */
    double[] rank (double[] data);
}
