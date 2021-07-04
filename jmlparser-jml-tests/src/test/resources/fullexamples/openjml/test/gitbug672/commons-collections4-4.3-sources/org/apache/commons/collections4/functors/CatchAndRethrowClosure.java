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
package org.apache.commons.collections4.functors;

import org.apache.commons.collections4.Closure;
import org.apache.commons.collections4.FunctorException;

/**
 * {@link Closure} that catches any checked exception and re-throws it as a
 * {@link FunctorException} runtime exception. Example usage:
 *
 * <pre>
 * // Create a catch and re-throw closure via anonymous subclass
 * CatchAndRethrowClosure&lt;String&gt; writer = new ThrowingClosure() {
 *     private java.io.Writer out = // some writer
 *
 *     protected void executeAndThrow(String input) throws IOException {
 *         out.write(input); // throwing of IOException allowed
 *     }
 * };
 *
 * // use catch and re-throw closure
 * java.util.List&lt;String&gt; strList = // some list
 * try {
 *     CollectionUtils.forAllDo(strList, writer);
 * } catch (FunctorException ex) {
 *     Throwable originalError = ex.getCause();
 *     // handle error
 * }
 * </pre>
 *
 * @since 4.0
 */
public abstract class CatchAndRethrowClosure<E> implements Closure<E> {

    /**
     * Execute this closure on the specified input object.
     *
     * @param input the input to execute on
     * @throws FunctorException (runtime) if the closure execution resulted in a
     *             checked exception.
     */
    @Override
    public void execute(final E input) {
        try {
            executeAndThrow(input);
        } catch (final RuntimeException ex) {
            throw ex;
        } catch (final Throwable t) {
            throw new FunctorException(t);
        }
    }

    /**
     * Execute this closure on the specified input object.
     *
     * @param input the input to execute on
     * @throws Throwable if the closure execution resulted in a checked
     *             exception.
     */
    protected abstract void executeAndThrow(E input) throws Throwable;
}
