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
import org.apache.commons.math3.optim.PointValuePair;

/**
 * A callback object that can be provided to a linear optimizer to keep track
 * of the best solution found.
 *
 * @since 3.3
 */
public class SolutionCallback implements OptimizationData {
    /** The SimplexTableau used by the SimplexSolver. */
    private SimplexTableau tableau;

    /**
     * Set the simplex tableau used during the optimization once a feasible
     * solution has been found.
     *
     * @param tableau the simplex tableau containing a feasible solution
     */
    void setTableau(final SimplexTableau tableau) {
        this.tableau = tableau;
    }

    /**
     * Retrieve the best solution found so far.
     * <p>
     * <b>Note:</b> the returned solution may not be optimal, e.g. in case
     * the optimizer did reach the iteration limits.
     *
     * @return the best solution found so far by the optimizer, or {@code null} if
     * no feasible solution could be found
     */
    public PointValuePair getSolution() {
        return tableau != null ? tableau.getSolution() : null;
    }

    /**
     * Returns if the found solution is optimal.
     * @return {@code true} if the solution is optimal, {@code false} otherwise
     */
    public boolean isSolutionOptimal() {
        return tableau != null ? tableau.isOptimal() : false;
    }
}
