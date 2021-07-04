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
package org.apache.commons.math3.genetics;

import org.apache.commons.math3.exception.MathIllegalArgumentException;
import org.apache.commons.math3.exception.util.Localizable;

/**
 * Exception indicating that the representation of a chromosome is not valid.
 *
 * @since 2.0
 */
public class InvalidRepresentationException extends MathIllegalArgumentException {

    /** Serialization version id */
    private static final long serialVersionUID = 1L;

    /**
     * Construct an InvalidRepresentationException with a specialized message.
     *
     * @param pattern Message pattern.
     * @param args Arguments.
     */
    public InvalidRepresentationException(Localizable pattern, Object ... args) {
       super(pattern, args);
    }

}
