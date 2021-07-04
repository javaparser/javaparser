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
package org.apache.commons.math3.ode;

import java.io.Serializable;

/** Simple container pairing a parameter name with a step in order to compute
 *  the associated Jacobian matrix by finite difference.
 *
 * @since 3.0
 */
class ParameterConfiguration implements Serializable {

    /** Serializable UID. */
    private static final long serialVersionUID = 2247518849090889379L;

    /** Parameter name. */
    private String parameterName;

    /** Parameter step for finite difference computation. */
    private double hP;

    /** Parameter name and step pair constructor.
     * @param parameterName parameter name
     * @param hP parameter step
     */
    ParameterConfiguration(final String parameterName, final double hP) {
        this.parameterName = parameterName;
        this.hP = hP;
    }

    /** Get parameter name.
     * @return parameterName parameter name
     */
    public String getParameterName() {
        return parameterName;
    }

    /** Get parameter step.
     * @return hP parameter step
     */
    public double getHP() {
        return hP;
    }

    /** Set parameter step.
     * @param hParam parameter step
     */
    public void setHP(final double hParam) {
        this.hP = hParam;
    }

}
