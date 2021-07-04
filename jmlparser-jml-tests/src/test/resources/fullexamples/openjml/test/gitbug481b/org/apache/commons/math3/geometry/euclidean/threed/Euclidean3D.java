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

package org.apache.commons.math3.geometry.euclidean.threed;

import java.io.Serializable;

import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.euclidean.twod.Euclidean2D;

/**
 * This class implements a three-dimensional space.
 * @since 3.0
 */
public class Euclidean3D implements Serializable, Space {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 6249091865814886817L;

    /** Private constructor for the singleton.
     */
    private Euclidean3D() {
    }

    /** Get the unique instance.
     * @return the unique instance
     */
    public static Euclidean3D getInstance() {
        return LazyHolder.INSTANCE;
    }

    /** {@inheritDoc} */
    public int getDimension() {
        return 3;
    }

    /** {@inheritDoc} */
    public Euclidean2D getSubSpace() {
        return Euclidean2D.getInstance();
    }

    // CHECKSTYLE: stop HideUtilityClassConstructor
    /** Holder for the instance.
     * <p>We use here the Initialization On Demand Holder Idiom.</p>
     */
    private static class LazyHolder {
        /** Cached field instance. */
        private static final Euclidean3D INSTANCE = new Euclidean3D();
    }
    // CHECKSTYLE: resume HideUtilityClassConstructor

    /** Handle deserialization of the singleton.
     * @return the singleton instance
     */
    private Object readResolve() {
        // return the singleton instance
        return LazyHolder.INSTANCE;
    }

}
