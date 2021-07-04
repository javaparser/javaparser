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

package org.apache.commons.math3.linear;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Exception to be thrown when a symmetric, definite positive
 * {@link RealLinearOperator} is expected.
 * Since the coefficients of the matrix are not accessible, the most
 * general definition is used to check that {@code A} is not positive
 * definite, i.e.  there exists {@code x} such that {@code x' A x <= 0}.
 * In the terminology of this exception, {@code A} is the "offending"
 * linear operator and {@code x} the "offending" vector.
 *
 * @since 3.0
 */
public class NonPositiveDefiniteOperatorException
    extends MathIllegalArgumentException {
    /** Serializable version Id. */
    private static final long serialVersionUID = 917034489420549847L;

    /** Creates a new instance of this class. */
    public NonPositiveDefiniteOperatorException() {
        super(LocalizedFormats.NON_POSITIVE_DEFINITE_OPERATOR);
    }
}
