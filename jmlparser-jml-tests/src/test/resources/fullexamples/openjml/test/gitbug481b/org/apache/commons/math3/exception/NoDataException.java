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
 * Exception to be thrown when the required data is missing.
 *
 * @since 2.2
 */
public class NoDataException extends MathIllegalArgumentException {

    /** Serializable version Id. */
    private static final long serialVersionUID = -3629324471511904459L;

    /**
     * Construct the exception.
     */
    public NoDataException() {
        this(LocalizedFormats.NO_DATA);
    }
    /**
     * Construct the exception with a specific context.
     *
     * @param specific Contextual information on what caused the exception.
     */
    public NoDataException(Localizable specific) {
        super(specific);
    }
}
