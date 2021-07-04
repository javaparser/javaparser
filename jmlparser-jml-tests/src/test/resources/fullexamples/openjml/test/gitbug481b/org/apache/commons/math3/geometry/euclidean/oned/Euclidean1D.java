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

package org.apache.commons.math3.geometry.euclidean.oned;

import java.io.Serializable;

import org.apache.commons.math3.exception.MathUnsupportedOperationException;
import org.apache.commons.math3.exception.util.LocalizedFormats;
import org.apache.commons.math3.geometry.Space;

/**
 * This class implements a one-dimensional space.
 * @since 3.0
 */
public class Euclidean1D implements Serializable, Space {

    /** Serializable version identifier. */
    private static final long serialVersionUID = -1178039568877797126L;

    /** Private constructor for the singleton.
     */
    private Euclidean1D() {
    }

    /** Get the unique instance.
     * @return the unique instance
     */
    public static Euclidean1D getInstance() {
        return LazyHolder.INSTANCE;
    }

    /** {@inheritDoc} */
    public int getDimension() {
        return 1;
    }

    /** {@inheritDoc}
     * <p>
     * As the 1-dimension Euclidean space does not have proper sub-spaces,
     * this method always throws a {@link NoSubSpaceException}
     * </p>
     * @return nothing
     * @throws NoSubSpaceException in all cases
     */
    public Space getSubSpace() throws NoSubSpaceException {
        throw new NoSubSpaceException();
    }

    // CHECKSTYLE: stop HideUtilityClassConstructor
    /** Holder for the instance.
     * <p>We use here the Initialization On Demand Holder Idiom.</p>
     */
    private static class LazyHolder {
        /** Cached field instance. */
        private static final Euclidean1D INSTANCE = new Euclidean1D();
    }
    // CHECKSTYLE: resume HideUtilityClassConstructor

    /** Handle deserialization of the singleton.
     * @return the singleton instance
     */
    private Object readResolve() {
        // return the singleton instance
        return LazyHolder.INSTANCE;
    }

    /** Specialized exception for inexistent sub-space.
     * <p>
     * This exception is thrown when attempting to get the sub-space of a one-dimensional space
     * </p>
     */
    public static class NoSubSpaceException extends MathUnsupportedOperationException {

        /** Serializable UID. */
        private static final long serialVersionUID = 20140225L;

        /** Simple constructor.
         */
        public NoSubSpaceException() {
            super(LocalizedFormats.NOT_SUPPORTED_IN_DIMENSION_N, 1);
        }

    }

}
