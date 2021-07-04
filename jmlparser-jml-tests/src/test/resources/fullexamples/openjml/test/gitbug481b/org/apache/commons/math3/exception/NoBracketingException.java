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
 * Exception to be thrown when function values have the same sign at both
 * ends of an interval.
 *
 * @since 3.0
 */
public class NoBracketingException extends MathIllegalArgumentException {
    /** Serializable version Id. */
    private static final long serialVersionUID = -3629324471511904459L;
    /** Lower end of the interval. */
    private final double lo;
    /** Higher end of the interval. */
    private final double hi;
    /** Value at lower end of the interval. */
    private final double fLo;
    /** Value at higher end of the interval. */
    private final double fHi;

    /**
     * Construct the exception.
     *
     * @param lo Lower end of the interval.
     * @param hi Higher end of the interval.
     * @param fLo Value at lower end of the interval.
     * @param fHi Value at higher end of the interval.
     */
    public NoBracketingException(double lo, double hi,
                                 double fLo, double fHi) {
        this(LocalizedFormats.SAME_SIGN_AT_ENDPOINTS, lo, hi, fLo, fHi);
    }

    /**
     * Construct the exception with a specific context.
     *
     * @param specific Contextual information on what caused the exception.
     * @param lo Lower end of the interval.
     * @param hi Higher end of the interval.
     * @param fLo Value at lower end of the interval.
     * @param fHi Value at higher end of the interval.
     * @param args Additional arguments.
     */
    public NoBracketingException(Localizable specific,
                                 double lo, double hi,
                                 double fLo, double fHi,
                                 Object ... args) {
        super(specific, Double.valueOf(lo), Double.valueOf(hi), Double.valueOf(fLo), Double.valueOf(fHi), args);
        this.lo = lo;
        this.hi = hi;
        this.fLo = fLo;
        this.fHi = fHi;
    }

    /**
     * Get the lower end of the interval.
     *
     * @return the lower end.
     */
    public double getLo() {
        return lo;
    }
    /**
     * Get the higher end of the interval.
     *
     * @return the higher end.
     */
    public double getHi() {
        return hi;
    }
    /**
     * Get the value at the lower end of the interval.
     *
     * @return the value at the lower end.
     */
    public double getFLo() {
        return fLo;
    }
    /**
     * Get the value at the higher end of the interval.
     *
     * @return the value at the higher end.
     */
    public double getFHi() {
        return fHi;
    }
}
