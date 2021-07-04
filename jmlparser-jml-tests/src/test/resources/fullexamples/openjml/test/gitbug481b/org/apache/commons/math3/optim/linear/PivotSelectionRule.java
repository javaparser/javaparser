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
package org.apache.commons.math3.optim.linear;

import org.apache.commons.math3.optim.OptimizationData;

/**
 * Pivot selection rule to the use for a Simplex solver.
 *
 * @since 3.3
 */
public enum PivotSelectionRule implements OptimizationData {
    /**
     * The classical rule, the variable with the most negative coefficient
     * in the objective function row will be chosen as entering variable.
     */
    DANTZIG,
    /**
     * The first variable with a negative coefficient in the objective function
     * row will be chosen as entering variable. This rule guarantees to prevent
     * cycles, but may take longer to find an optimal solution.
     */
    BLAND
}
