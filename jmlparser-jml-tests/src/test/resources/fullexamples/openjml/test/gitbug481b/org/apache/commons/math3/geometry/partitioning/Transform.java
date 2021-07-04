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
package org.apache.commons.math3.geometry.partitioning;

import org.apache.commons.math3.geometry.Point;
import org.apache.commons.math3.geometry.Space;


/** This interface represents an inversible affine transform in a space.
 * <p>Inversible affine transform include for example scalings,
 * translations, rotations.</p>

 * <p>Transforms are dimension-specific. The consistency rules between
 * the three {@code apply} methods are the following ones for a
 * transformed defined for dimension D:</p>
 * <ul>
 *   <li>
 *     the transform can be applied to a point in the
 *     D-dimension space using its {@link #apply(Point)}
 *     method
 *   </li>
 *   <li>
 *     the transform can be applied to a (D-1)-dimension
 *     hyperplane in the D-dimension space using its
 *     {@link #apply(Hyperplane)} method
 *   </li>
 *   <li>
 *     the transform can be applied to a (D-2)-dimension
 *     sub-hyperplane in a (D-1)-dimension hyperplane using
 *     its {@link #apply(SubHyperplane, Hyperplane, Hyperplane)}
 *     method
 *   </li>
 * </ul>

 * @param <S> Type of the embedding space.
 * @param <T> Type of the embedded sub-space.

 * @since 3.0
 */
public interface Transform<S extends Space, T extends Space> {

    /** Transform a point of a space.
     * @param point point to transform
     * @return a new object representing the transformed point
     */
    Point<S> apply(Point<S> point);

    /** Transform an hyperplane of a space.
     * @param hyperplane hyperplane to transform
     * @return a new object representing the transformed hyperplane
     */
    Hyperplane<S> apply(Hyperplane<S> hyperplane);

    /** Transform a sub-hyperplane embedded in an hyperplane.
     * @param sub sub-hyperplane to transform
     * @param original hyperplane in which the sub-hyperplane is
     * defined (this is the original hyperplane, the transform has
     * <em>not</em> been applied to it)
     * @param transformed hyperplane in which the sub-hyperplane is
     * defined (this is the transformed hyperplane, the transform
     * <em>has</em> been applied to it)
     * @return a new object representing the transformed sub-hyperplane
     */
    SubHyperplane<T> apply(SubHyperplane<T> sub, Hyperplane<S> original, Hyperplane<S> transformed);

}
