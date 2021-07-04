/**
 *  This file is part of miniCDx benchmark of oSCJ.
 *
 *   miniCDx is free software: you can redistribute it and/or modify
 *   it under the terms of the GNU Lesser General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or
 *   (at your option) any later version.
 *
 *   miniCDx is distributed in the hope that it will be useful,
 *   but WITHOUT ANY WARRANTY; without even the implied warranty of
 *   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 *   GNU Lesser General Public License for more details.
 *
 *   You should have received a copy of the GNU Lesser General Public License
 *   along with miniCDx.  If not, see <http://www.gnu.org/licenses/>.
 *
 *
 *   Copyright 2009, 2010 
 *   @authors  Daniel Tang, Ales Plsek
 *
 *   See: http://sss.cs.purdue.edu/projects/oscj/
 */
package minicdj.cdx;

import minicdj.collision.Vector3d;

/**
 * Objects of the <code>Motion</code> class provide all a-priori known information about what the Aircraft was doing
 * between two frames. Also provides methods to do useful things with this object (so it's not just dead data).
 * 
 * @author Filip Pizlo
 */
/*@javax.safetycritical.annotate.Scope("cdx.CollisionDetectorHandler")*/
class Motion {
    /** The aircraft that we are referring to. */
    private final Aircraft aircraft;
    /**
     * The first position (from the last frame). Will be equal to <code>pos_two</code> if we do not have a record for
     * this aircraft for any previous frames.
     */
    private final Vector3d pos_one;
    /** The second position (from the current frame). */
    private final Vector3d pos_two;

    /** Initialize with an aircraft and two positions. */
    public Motion(final Aircraft _aircraft, final Vector3d _pos_one, final Vector3d _pos_two) {
        aircraft = _aircraft;
        pos_one = _pos_one;
        pos_two = _pos_two;
    }

    /** Initialize with an aircraft and one position. */
    public Motion(final Aircraft _aircraft, final Vector3d _pos) {
        this(_aircraft, _pos, _pos);
    }

    /** Retrieve the aircraft. */
    public Aircraft getAircraft() {
        return aircraft;
    }

    /** Retrieve position #1. */
    public Vector3d getFirstPosition() {
        return pos_one;
    }

    /** Retrieve position #2. */
    public Vector3d getSecondPosition() {
        return pos_two;
    }

    public String toString() {
        return "MOTION of " + getAircraft().toString() + " from " + getFirstPosition().toString() + " to "
                + getSecondPosition().toString();
    }

    /**
     * Find an intersection between this Motion and another.
     * 
     * @return a Vector3d object with the intersection point if an intersection was found, null otherwise.
     * @author Jeff Hagelberg, Filip Pizlo
     */

    // see the code for checking the (strange) semantics of the returned intersection

    public Vector3d findIntersection(final Motion other) {
        final Vector3d i1 = new Vector3d(), f1 = new Vector3d(), i2 = new Vector3d(), f2 = new Vector3d();
        i1.set(getFirstPosition());
        f1.set(getSecondPosition());
        i2.set(other.getFirstPosition());
        f2.set(other.getSecondPosition());
        float r = Constants.PROXIMITY_RADIUS;
        final float vx1 = f1.x - i1.x;
        final float vx2 = f2.x - i2.x;
        final float vy1 = f1.y - i1.y;
        final float vy2 = f2.y - i2.y;
        final float vz1 = f1.z - i1.z;
        final float vz2 = f2.z - i2.z;

        // this test is not geometrical 3-d intersection test, it takes the fact that the aircraft move
        // into account ; so it is more like a 4d test
        // (it assumes that both of the aircraft have a constant speed over the tested interval)

        // we thus have two points, each of them moving on its line segment at constant speed ; we are looking
        // for times when the distance between these two points is smaller than r

        // V1 is vector of aircraft 1
        // V2 is vector of aircraft 2

        // if a = 0 iff the planes are moving in parallel and have the same speed (can be zero - they may not be moving
        // at all)

        // a = (V2 - V1)^T * (V2 - V1) = < (V2 - V1), (V2 - V1) > = sqrt( || V2 - V1 || )
        final float a = (vx2 - vx1) * (vx2 - vx1) + (vy2 - vy1) * (vy2 - vy1) + (vz2 - vz1) * (vz2 - vz1);

        if (a != 0.0f) {

            // we are first looking for instances of time when the planes are exactly r from each other
            // at least one plane is moving ; if the planes are moving in parallel, they do not have constant speed

            // if the planes are moving in parallel, then
            // if the faster starts behind the slower, we can have 2, 1, or 0 solutions
            // if the faster plane starts in front of the slower, we can have 0 or 1 solutions

            // if the planes are not moving in parallel, then

            // point P1 = I1 + vV1
            // point P2 = I2 + vV2
            // - looking for v, such that dist(P1,P2) = || P1 - P2 || = r

            // it follows that || P1 - P2 || = sqrt( < P1-P2, P1-P2 > )
            // 0 = -r^2 + < P1 - P2, P1 - P2 >
            // from properties of dot product
            // 0 = -r^2 + <I1-I2,I1-I2> + v * 2<I1-I2, V1-V2> + v^2 *<V1-V2,V1-V2>
            // so we calculate a, b, c - and solve the quadratic equation
            // 0 = c + bv + av^2

            // b = 2 * <I1-I2, V1-V2>
            float b = 2.0f * (i2.x * vx2 - i2.x * vx1 - i1.x * vx2 + i1.x * vx1 + i2.y * vy2 - i2.y * vy1 - i1.y * vy2
                    + i1.y * vy1 + i2.z * vz2 - i2.z * vz1 - i1.z * vz2 + i1.z * vz1);

            // c = -r^2 + (I2 - I1)^T * (I2 - I1)
            final float c = -r * r + (i2.x - i1.x) * (i2.x - i1.x) + (i2.y - i1.y) * (i2.y - i1.y) + (i2.z - i1.z)
                    * (i2.z - i1.z);

            final float discr = b * b - 4.0f * a * c;
            if (discr < 0.0f) return null;

            // the left side
            final float v1 = (-b - (float) Math.sqrt(discr)) / (2.0f * a);
            // the right side
            final float v2 = (-b + (float) Math.sqrt(discr)) / (2.0f * a);

            // FIXME: v1 <= v2 always holds, correct ?
            // .. because v1 > v2 only if a < 0, which would mean <V1-V2,V1-V2> < 0, which is impossible

            if (v1 <= v2 && (v1 <= 1.0f && 1.0f <= v2 || v1 <= 0.0f && 0.0f <= v2 || 0.0f <= v1 && v2 <= 1.0f)) {
                // new: calculate the location of the collision; if it is
                // outside of the bounds of the Simulation, don't do anything!
                final float x1col = i1.x + vx1 * (v1 + v2) / 2.0f;
                final float y1col = i1.y + vy1 * (v1 + v2) / 2.0f;
                final float z1col = i1.z + vz1 * (v1 + v2) / 2.0f;
                if (z1col > Constants.MIN_Z && z1col <= Constants.MAX_Z && x1col >= Constants.MIN_X
                        && x1col <= Constants.MAX_X && y1col >= Constants.MIN_Y && y1col <= Constants.MAX_Y) return new Vector3d(
                    x1col, y1col, z1col);
            }
        } else {

            // the planes have the same speeds and are moving in parallel (or they are not moving at all)
            // they thus have the same distance all the time ; we calculate it from the initial point

            // dist = || i2 - i1 || = sqrt( ( i2 - i1 )^T * ( i2 - i1 ) )

            float dist = (i2.x - i1.x) * (i2.x - i1.x) + (i2.y - i1.y) * (i2.y - i1.y) + (i2.z - i1.z) * (i2.z - i1.z);
            dist = (float) Math.sqrt(dist);

            // devices.Console.println("i1 = "+i1+", i2 = "+i2+", dist = "+dist);
            if (dist <= r)
            // devices.Console.println("Planes were travelling in parallel. Collision.");
            return getFirstPosition();
        }
        return null;
    }
}
