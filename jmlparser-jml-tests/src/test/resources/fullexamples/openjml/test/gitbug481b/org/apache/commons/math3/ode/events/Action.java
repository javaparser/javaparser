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

package org.apache.commons.math3.ode.events;

/** Enumerate for actions to be performed when an event occurs during ODE integration.
 * @since 3.6
 */
public enum Action {

    /** Stop indicator.
     * <p>This value should be used as the return value of the {@code
     * eventOccurred} method when the integration should be
     * stopped after the event ending the current step.</p>
     */
    STOP,

    /** Reset state indicator.
     * <p>This value should be used as the return value of the {@code
     * eventOccurred}} method when the integration should
     * go on after the event ending the current step, with a new state
     * vector (which will be retrieved thanks to the {@code resetState}
     * method).</p>
     */
    RESET_STATE,

    /** Reset derivatives indicator.
     * <p>This value should be used as the return value of the {@code
     * eventOccurred} method when the integration should
     * go on after the event ending the current step, with a new derivatives
     * vector.</p>
     */
    RESET_DERIVATIVES,

    /** Continue indicator.
     * <p>This value should be used as the return value of the {@code
     * eventOccurred} method when the integration should go
     * on after the event ending the current step.</p>
     */
    CONTINUE;

}
