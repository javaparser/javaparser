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
 * Defines a functor interface implemented by classes that do something.
 * <p>
 * A <code>Closure</code> represents a block of code which is executed from
 * inside some block, function or iteration. It operates an input object.
 * <p>
 * Standard implementations of common closures are provided by
 * {@link ClosureUtils}. These include method invocation and for/while loops.
 *
 * @param <T> the type that the closure acts on
 * @since 1.0
 */
public interface Closure<T> {

    /**
     * Performs an action on the specified input object.
     *
     * @param input  the input to execute on
     * @throws ClassCastException (runtime) if the input is the wrong class
     * @throws IllegalArgumentException (runtime) if the input is invalid
     * @throws FunctorException (runtime) if any other error occurs
     */
    void execute(T input);

}
