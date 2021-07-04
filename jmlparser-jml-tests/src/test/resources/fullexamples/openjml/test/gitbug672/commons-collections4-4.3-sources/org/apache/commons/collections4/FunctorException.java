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
package org.apache.commons.collections4;

/**
 * Runtime exception thrown from functors.
 * If required, a root cause error can be wrapped within this one.
 *
 * @since 3.0
 */
public class FunctorException extends RuntimeException {

    /** Serialization version */
    private static final long serialVersionUID = -4704772662059351193L;

    /**
     * Constructs a new <code>FunctorException</code> without specified
     * detail message.
     */
    public FunctorException() {
        super();
    }

    /**
     * Constructs a new <code>FunctorException</code> with specified
     * detail message.
     *
     * @param msg  the error message.
     */
    public FunctorException(final String msg) {
        super(msg);
    }

    /**
     * Constructs a new <code>FunctorException</code> with specified
     * nested <code>Throwable</code> root cause.
     *
     * @param rootCause  the exception or error that caused this exception
     *                   to be thrown.
     */
    public FunctorException(final Throwable rootCause) {
        super(rootCause);
    }

    /**
     * Constructs a new <code>FunctorException</code> with specified
     * detail message and nested <code>Throwable</code> root cause.
     *
     * @param msg        the error message.
     * @param rootCause  the exception or error that caused this exception
     *                   to be thrown.
     */
    public FunctorException(final String msg, final Throwable rootCause) {
        super(msg, rootCause);
    }

}
