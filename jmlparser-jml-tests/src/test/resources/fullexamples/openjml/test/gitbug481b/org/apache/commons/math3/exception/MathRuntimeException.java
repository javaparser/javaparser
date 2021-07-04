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
import org.apache.commons.math3.exception.util.ExceptionContext;
import org.apache.commons.math3.exception.util.ExceptionContextProvider;

/**
 * As of release 4.0, all exceptions thrown by the Commons Math code (except
 * {@link NullArgumentException}) inherit from this class.
 * In most cases, this class should not be instantiated directly: it should
 * serve as a base class for implementing exception classes that describe a
 * specific "problem".
 *
 * @since 3.1
 */
public class MathRuntimeException extends RuntimeException
    implements ExceptionContextProvider {
    /** Serializable version Id. */
    private static final long serialVersionUID = 20120926L;
    /** Context. */
    private final ExceptionContext context;

    /**
     * @param pattern Message pattern explaining the cause of the error.
     * @param args Arguments.
     */
    public MathRuntimeException(Localizable pattern,
                                Object ... args) {
        context = new ExceptionContext(this);
        context.addMessage(pattern, args);
    }

    /** {@inheritDoc} */
    public ExceptionContext getContext() {
        return context;
    }

    /** {@inheritDoc} */
    @Override
    public String getMessage() {
        return context.getMessage();
    }

    /** {@inheritDoc} */
    @Override
    public String getLocalizedMessage() {
        return context.getLocalizedMessage();
    }
}
