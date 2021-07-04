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

/**
 * This enumerates is used to differentiate the semantics of a rotation.
 * @see Rotation
 * @since 3.6
 */
public enum RotationConvention {

    /** Constant for rotation that have the semantics of a vector operator.
     * <p>
     * According to this convention, the rotation moves vectors with respect
     * to a fixed reference frame.
     * </p>
     * <p>
     * This means that if we define rotation r is a 90 degrees rotation around
     * the Z axis, the image of vector {@link Vector3D#PLUS_I} would be
     * {@link Vector3D#PLUS_J}, the image of vector {@link Vector3D#PLUS_J}
     * would be {@link Vector3D#MINUS_I}, the image of vector {@link Vector3D#PLUS_K}
     * would be {@link Vector3D#PLUS_K}, and the image of vector with coordinates (1, 2, 3)
     * would be vector (-2, 1, 3). This means that the vector rotates counterclockwise.
     * </p>
     * <p>
     * This convention was the only one supported by Apache Commons Math up to version 3.5.
     * </p>
     * <p>
     * The difference with {@link #FRAME_TRANSFORM} is only the semantics of the sign
     * of the angle. It is always possible to create or use a rotation using either
     * convention to really represent a rotation that would have been best created or
     * used with the other convention, by changing accordingly the sign of the
     * rotation angle. This is how things were done up to version 3.5.
     * </p>
     */
    VECTOR_OPERATOR,

    /** Constant for rotation that have the semantics of a frame conversion.
     * <p>
     * According to this convention, the rotation considered vectors to be fixed,
     * but their coordinates change as they are converted from an initial frame to
     * a destination frame rotated with respect to the initial frame.
     * </p>
     * <p>
     * This means that if we define rotation r is a 90 degrees rotation around
     * the Z axis, the image of vector {@link Vector3D#PLUS_I} would be
     * {@link Vector3D#MINUS_J}, the image of vector {@link Vector3D#PLUS_J}
     * would be {@link Vector3D#PLUS_I}, the image of vector {@link Vector3D#PLUS_K}
     * would be {@link Vector3D#PLUS_K}, and the image of vector with coordinates (1, 2, 3)
     * would be vector (2, -1, 3). This means that the coordinates of the vector rotates
     * clockwise, because they are expressed with respect to a destination frame that is rotated
     * counterclockwise.
     * </p>
     * <p>
     * The difference with {@link #VECTOR_OPERATOR} is only the semantics of the sign
     * of the angle. It is always possible to create or use a rotation using either
     * convention to really represent a rotation that would have been best created or
     * used with the other convention, by changing accordingly the sign of the
     * rotation angle. This is how things were done up to version 3.5.
     * </p>
     */
    FRAME_TRANSFORM;

}
