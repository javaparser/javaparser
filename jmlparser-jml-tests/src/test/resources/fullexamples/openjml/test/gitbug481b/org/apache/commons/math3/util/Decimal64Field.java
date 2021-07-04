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
package org.apache.commons.math3.util;

import org.apache.commons.math3.Field;
import org.apache.commons.math3.FieldElement;

/**
 * The field of double precision floating-point numbers.
 *
 * @since 3.1
 * @see Decimal64
 */
public class Decimal64Field implements Field<Decimal64> {

    /** The unique instance of this class. */
    private static final Decimal64Field INSTANCE = new Decimal64Field();

    /** Default constructor. */
    private Decimal64Field() {
        // Do nothing
    }

    /**
     * Returns the unique instance of this class.
     *
     * @return the unique instance of this class
     */
    public static final Decimal64Field getInstance() {
        return INSTANCE;
    }

    /** {@inheritDoc} */
    public Decimal64 getZero() {
        return Decimal64.ZERO;
    }

    /** {@inheritDoc} */
    public Decimal64 getOne() {
        return Decimal64.ONE;
    }

    /** {@inheritDoc} */
    public Class<? extends FieldElement<Decimal64>> getRuntimeClass() {
        return Decimal64.class;
    }
}
