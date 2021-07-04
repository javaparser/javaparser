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
 * The <code>VectorConstants</code> class implements some simple utility methods for obtaining vectors that are commonly
 * used, such as zero vectors, unit direction vectors, and orthogonal vectors.
 * 
 * @author Ben L. Titzer
 */
final class VectorConstants {

    public static final int NO_QUADRANT = 0;
    public static final int NE_QUADRANT = 1;
    public static final int NW_QUADRANT = 2;
    public static final int SE_QUADRANT = 4;
    public static final int SW_QUADRANT = 3;

    /**
     * The <code>west</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "west" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void west(Vector3d dest) {
        dest.x = -1;
        dest.y = 0;
        dest.z = 0;
    }

    /**
     * The <code>east</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "east" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void east(Vector3d dest) {
        dest.x = 1;
        dest.y = 0;
        dest.z = 0;
    }

    /**
     * The <code>north</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "north" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void north(Vector3d dest) {
        dest.x = 0;
        dest.y = 1;
        dest.z = 0;
    }

    /**
     * The <code>south</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "south" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void south(Vector3d dest) {
        dest.x = 0;
        dest.y = -1;
        dest.z = 0;
    }

    /**
     * The <code>up</code> method is a utility function that will set the destination operand to a unit vector pointing
     * in the "up" direction. This family of functions has been added for convenient access to the common orthogonal
     * directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void up(Vector3d dest) {
        dest.x = 0;
        dest.y = 0;
        dest.z = 1;
    }

    /**
     * The <code>down</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "down" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void down(Vector3d dest) {
        dest.x = 0;
        dest.y = 0;
        dest.z = -1;
    }

    /**
     * The <code>direction</code> method is a utility function that will return a unit vector in the direction
     * specified. It takes an argument in degrees and a vector destination where it stores the result.
     * 
     * @param deg
     *            the angle's value in degrees
     * @param dest
     *            the vector in which to store the result
     */
    public static void direction(float deg, Vector3d dest) {
        double radians = Math.PI * deg / 180;
        dest.x = (float) Math.cos(radians);
        dest.y = (float) Math.sin(radians);
        dest.z = 0;
    }

    /**
     * The <code>west</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "west" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void west(Vector2d dest) {
        dest.x = -1;
        dest.y = 0;
    }

    /**
     * The <code>east</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "east" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void east(Vector2d dest) {
        dest.x = 1;
        dest.y = 0;
    }

    /**
     * The <code>north</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "north" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void north(Vector2d dest) {
        dest.x = 0;
        dest.y = 1;
    }

    /**
     * The <code>south</code> method is a utility function that will set the destination operand to a unit vector
     * pointing in the "south" direction. This family of functions has been added for convenient access to the common
     * orthogonal directions.
     * 
     * @param dest
     *            the vector in which to store the result
     */
    public static void south(Vector2d dest) {
        dest.x = 0;
        dest.y = -1;
    }

    /**
     * The <code>direction</code> method is a utility function that will return a unit vector in the direction
     * specified. It takes an argument in degrees and a vector destination where it stores the result.
     * 
     * @param deg
     *            the angle's value in degrees
     * @param dest
     *            the vector in which to store the result
     */
    public static void direction(float deg, Vector2d dest) {
        double radians = Math.PI * deg / 180;
        dest.x = (float) Math.cos(radians);
        dest.y = (float) Math.sin(radians);
    }
}
