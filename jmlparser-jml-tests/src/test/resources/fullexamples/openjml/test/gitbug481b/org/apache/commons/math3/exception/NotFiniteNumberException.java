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
 * Exception to be thrown when a number is not finite.
 *
 * @since 3.0
 */
public class NotFiniteNumberException extends MathIllegalNumberException {
    /** Serializable version Id. */
    private static final long serialVersionUID = -6100997100383932834L;

    /**
     * Construct the exception.
     *
     * @param wrong Value that is infinite or NaN.
     * @param args Optional arguments.
     */
    public NotFiniteNumberException(Number wrong,
                                    Object ... args) {
        this(LocalizedFormats.NOT_FINITE_NUMBER, wrong, args);
    }

    /**
     * Construct the exception with a specific context.
     *
     * @param specific Specific context pattern.
     * @param wrong Value that is infinite or NaN.
     * @param args Optional arguments.
     */
    public NotFiniteNumberException(Localizable specific,
                                    Number wrong,
                                    Object ... args) {
        super(specific, wrong, args);
    }
}
