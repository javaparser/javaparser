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

package org.apache.commons.math3.geometry.spherical.twod;

import java.io.Serializable;

import org.apache.commons.math3.geometry.Space;
import org.apache.commons.math3.geometry.spherical.oned.Sphere1D;

/**
 * This class implements a two-dimensional sphere (i.e. the regular sphere).
 * <p>
 * We use here the topologists definition of the 2-sphere (see
 * <a href="http://mathworld.wolfram.com/Sphere.html">Sphere</a> on
 * MathWorld), i.e. the 2-sphere is the two-dimensional surface
 * defined in 3D as x<sup>2</sup>+y<sup>2</sup>+z<sup>2</sup>=1.
 * </p>
 * @since 3.3
 */
public class Sphere2D implements Serializable, Space {

    /** Serializable version identifier. */
    private static final long serialVersionUID = 20131218L;

    /** Private constructor for the singleton.
     */
    private Sphere2D() {
    }

    /** Get the unique instance.
     * @return the unique instance
     */
    public static Sphere2D getInstance() {
        return LazyHolder.INSTANCE;
    }

    /** {@inheritDoc} */
    public int getDimension() {
        return 2;
    }

    /** {@inheritDoc} */
    public Sphere1D getSubSpace() {
        return Sphere1D.getInstance();
    }

    // CHECKSTYLE: stop HideUtilityClassConstructor
    /** Holder for the instance.
     * <p>We use here the Initialization On Demand Holder Idiom.</p>
     */
    private static class LazyHolder {
        /** Cached field instance. */
        private static final Sphere2D INSTANCE = new Sphere2D();
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
