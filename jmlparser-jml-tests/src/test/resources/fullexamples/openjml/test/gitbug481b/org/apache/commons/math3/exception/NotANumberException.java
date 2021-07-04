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

import org.apache.commons.math3.exception.util.LocalizedFormats;

/**
 * Exception to be thrown when a number is not a number.
 *
 * @since 3.1
 */
public class NotANumberException extends MathIllegalNumberException {
    /** Serializable version Id. */
    private static final long serialVersionUID = 20120906L;

    /**
     * Construct the exception.
     */
    public NotANumberException() {
        super(LocalizedFormats.NAN_NOT_ALLOWED, Double.valueOf(Double.NaN));
    }

}
