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

/**
 * Types of relationships between two cells in a Solver {@link LinearConstraint}.
 *
 * @since 2.0
 */
public enum Relationship {
    /** Equality relationship. */
    EQ("="),
    /** Lesser than or equal relationship. */
    LEQ("<="),
    /** Greater than or equal relationship. */
    GEQ(">=");

    /** Display string for the relationship. */
    private final String stringValue;

    /**
     * Simple constructor.
     *
     * @param stringValue Display string for the relationship.
     */
    Relationship(String stringValue) {
        this.stringValue = stringValue;
    }

    /** {@inheritDoc} */
    @Override
    public String toString() {
        return stringValue;
    }

    /**
     * Gets the relationship obtained when multiplying all coefficients by -1.
     *
     * @return the opposite relationship.
     */
    public Relationship oppositeRelationship() {
        switch (this) {
        case LEQ :
            return GEQ;
        case GEQ :
            return LEQ;
        default :
            return EQ;
        }
    }
}
