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
 * The <code>VectorMath</code> class implements the mathematical functions for manipulating vectors of two and three
 * dimensions. Its operators are patterned after three address code machines, specifying two operands and a destination
 * operand. This machine is optimized for performance, thus the methods are static, contain no calls, create no objects,
 * and do not perform error checking or synchronization.
 * 
 * @author Ben L. Titzer
 */
final class VectorMath {

    /***********************************************************************************************
     * 3 D V e c t o r C o m p u t a t i o n s
     **********************************************************************************************/

    /**
     * The <code>add</code> method takes two vectors and adds them, placing the result in a third vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @param dest
     *            the destination Vector3d to store the result
     */
    public static void add(Vector3d a, Vector3d b, Vector3d dest) {
        dest.x = a.x + b.x;
        dest.y = a.y + b.y;
        dest.z = a.z + b.z;
    }

    /**
     * The <code>subtract</code> method takes two vectors and subtracts them, placing the result in a third vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @param dest
     *            the destination Vector3d to store the result
     */
    public static void subtract(Vector3d a, Vector3d b, Vector3d dest) {
        dest.x = a.x - b.x;
        dest.y = a.y - b.y;
        dest.z = a.z - b.z;
    }

    /**
     * The <code>scale</code> method takes a <code>Vector3d</code> and a scalar float value multiplies each component of
     * the Vector, storing the result in the third parameter.
     * 
     * @param a
     *            the value of the first vector
     * @param scale
     *            the value to scale the vector by
     * @param dest
     *            the destination Vector3d to store the result
     */
    public static void scale(Vector3d a, float scale, Vector3d dest) {
        dest.x = a.x * scale;
        dest.y = a.y * scale;
        dest.z = a.z * scale;
    }

    /**
     * The <code>normalize</code> method takes a <code>Vector3d</code> and if it is non-zero, will normalize it so that
     * its magnitude will be 1.
     * 
     * @param a
     *            the value of the vector to normalize
     * @param dest
     *            the destination Vector3d to store the result
     * @throws ZeroVectorException
     *             if the vector is zero
     */
    public static void normalize(Vector3d a, Vector3d dest) {
        float mag = magnitude(a);
        if (mag == 0) throw new ZeroVectorException("undefined");
        scale(a, 1 / mag, dest);
    }

    /**
     * The <code>magnitude</code> method takes a <code>Vector3d</code> and computes its magnitude according the
     * Euclidean norm.
     * 
     * @param a
     *            the value of the vector of which to compute the magnitude
     * @returns the magnitude of the vector
     */
    public static float magnitude(Vector3d a) {
        return (float) Math.sqrt(a.x * a.x + a.y * a.y + a.z * a.z);
    }

    /**
     * The <code>distance</code> method takes two vectors and computes their (Euclidean) distance.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the distance between the two vectors
     */
    public static float distance(Vector3d a, Vector3d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        float dz = a.z - b.z;
        return (float) Math.sqrt(dx * dx + dy * dy + dz * dz);
    }

    /**
     * The <code>sqDistance</code> method takes two vectors and computes the square of their (Euclidean) distance. This
     * is just an optimization for the <code>distance</code> method that avoids an expensive floating point square root
     * computation.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the square of the distance between the two vectors
     */
    public static float sqDistance(Vector3d a, Vector3d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        float dz = a.z - b.z;
        return dx * dx + dy * dy + dz * dz;
    }

    /**
     * The <code>dotProduct</code> method computes the dot product between two vectors using the standard inner product
     * formula.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the value of their dot product
     */
    public static float dotProduct(Vector3d a, Vector3d b) {
        return a.x * b.x + a.y * b.y + a.z * b.z;
    }

    /**
     * The <code>rotate</code> method takes a <code>Vector3d</code> and a scalar float value and will rotate the vector
     * in the xy plane.
     * 
     * @param a
     *            the value of the first vector
     * @param radians
     *            the value to rotate the vector by
     * @param dest
     *            the destination Vector3d to store the result
     */
    public static void rotate(Vector3d a, float radians, Vector3d dest) {
        float cos = (float) Math.cos(radians);
        float sin = (float) Math.sin(radians);
        float x = a.x, y = a.y;
        dest.x = x * cos - y * sin;
        dest.y = x * sin + y * cos;
        dest.z = a.z;
    }

    /**
     * The <code>theta</code> method takes a <code>Vector3d</code> and calculates the angle between the X-axis and the
     * vector, ignoring the z component of the vector.
     * 
     * @param a
     *            the vector of which to calculate the theta angle
     * @returns the radian value in the range [0, 2*pi] that represents the angle between the x axis and this vector (in
     *          the xy plane)
     * @throws ZeroVectorException
     *             if the vector passed equals the zero vector, for which the theta value is undefined
     */
    public static float theta(Vector3d a) {
        float x = a.x, y = a.y;
        if (x == 0) { // tangent undefined for x = 0
            if (y == 0) throw new ZeroVectorException("undefined");
            if (y < 0) return (float) (1.5 * Math.PI);
            return (float) (0.5 * Math.PI);
        }
        float t = (float) Math.atan(y / x); // calculate theta

        if (x < 0) return (float) Math.PI - t; // adjust quadrant
        if (t < 0) t += 2 * Math.PI; // range adjustment [0, 2*pi]

        return t;
    }

    /**
     * The <code>phi</code> method takes a <code>Vector3d</code> and calculates the elevation between the XY-plane and
     * the vector.
     * 
     * @param a
     *            the vector of which to calculate the phi angle
     * @returns the radian value in the range [-pi/2, pi/2] that represents the angle between the x axis and this vector
     *          (in the xy plane)
     * @throws ZeroVectorException
     *             if the vector passed equals the zero vector, for which the phi value is undefined
     */
    public static float phi(Vector3d a) {
        float x = a.x, y = a.y, z = a.z;
        if (x == 0 && y == 0) { // tangent undefined for h = 0
            if (z == 0) throw new ZeroVectorException("undefined");
            if (z < 0) return (float) (-0.5 * Math.PI);
            return (float) (0.5 * Math.PI);
        }
        float h = (float) Math.sqrt(x * x + y * y);
        float t = (float) Math.atan(y / h); // calculate phi

        return t;
    }

    /***********************************************************************************************
     * 2 D V e c t o r C o m p u t a t i o n s
     **********************************************************************************************/

    /**
     * The <code>add</code> method takes two vectors and adds them, placing the result in a third vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @param dest
     *            the destination Vector2d to store the result
     */
    public static void add(Vector2d a, Vector2d b, Vector2d dest) {
        dest.x = a.x + b.x;
        dest.y = a.y + b.y;
    }

    /**
     * The <code>subtract</code> method takes two vectors and subtracts them, placing the result in a third vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @param dest
     *            the destination Vector2d to store the result
     */
    public static void subtract(Vector2d a, Vector2d b, Vector2d dest) {
        dest.x = a.x - b.x;
        dest.y = a.y - b.y;
    }

    /**
     * The <code>scale</code> method takes a <code>Vector2d</code> and a scalar float value multiplies each component of
     * the Vector, storing the result in the third parameter.
     * 
     * @param a
     *            the value of the first vector
     * @param scale
     *            the value to scale the vector by
     * @param dest
     *            the destination Vector2d to store the result
     */
    public static void scale(Vector2d a, float scale, Vector2d dest) {
        dest.x = a.x * scale;
        dest.y = a.y * scale;
    }

    /**
     * The <code>normalize</code> method takes a <code>Vector2d</code> and if it is non-zero, will normalize it so that
     * its magnitude will be 1.
     * 
     * @param a
     *            the value of the vector to normalize
     * @param dest
     *            the destination Vector2d to store the result
     * @throws ZeroVectorException
     *             if the vector is zero
     */
    public static void normalize(Vector2d a, Vector2d dest) {
        float mag = magnitude(a);
        if (mag == 0) throw new ZeroVectorException("undefined");
        scale(a, 1 / mag, dest);
    }

    /**
     * The <code>magnitude</code> method takes a <code>Vector2d</code> and computes its magnitude according the
     * Euclidean norm.
     * 
     * @param a
     *            the value of the vector of which to compute the magnitude
     * @returns the magnitude of the vector
     */
    public static float magnitude(Vector2d a) {
        return (float) Math.sqrt(a.x * a.x + a.y * a.y);
    }

    /**
     * The <code>distance</code> method takes two vectors and computes their (Euclidean) distance.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the distance between the two vectors
     */
    public static float distance(Vector2d a, Vector2d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return (float) Math.sqrt(dx * dx + dy * dy);
    }

    /**
     * The <code>sqDistance</code> method takes two vectors and computes the square of their (Euclidean) distance. This
     * is just an optimization for the <code>distance</code> method that avoids an expensive floating point square root
     * computation.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the square of the distance between the two vectors
     */
    public static float sqDistance(Vector2d a, Vector2d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return dx * dx + dy * dy;
    }

    /**
     * The <code>dotProduct</code> method computes the dot product between two vectors using the standard inner product
     * formula.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the value of their dot product
     */
    public static float dotProduct(Vector2d a, Vector2d b) {
        return a.x * b.x + a.y * b.y;
    }

    /**
     * The <code>quadrant</code> method is a utility function for two dimensional vectors that takes a vector as a
     * parameter and will return an integer describing what quadrant of the xy plane the vector lies in.
     * 
     * @param a
     *            the vector to compute the quadrant of
     * @returns the integer VectorConstants.XX_QUADRANT value corresponding to which quadrant the vector lies in
     */
    public static int quadrant(Vector2d a) {
        float x = a.x, y = a.y;
        float xy = x * y;

        if (xy == 0) return VectorConstants.NO_QUADRANT; // lies on axis

        if (xy > 0) {
            if (x > 0) return VectorConstants.NE_QUADRANT;
            else return VectorConstants.SW_QUADRANT;
        } else {
            if (x < 0) return VectorConstants.NW_QUADRANT;
            else return VectorConstants.SE_QUADRANT;
        }
    }

    /***********************************************************************************************
     * 2 D / 3 D M i x e d C o m p u t a t i o n s
     **********************************************************************************************/

    /**
     * The <code>convert</code> methods have been overridden to allow 2d vectors to be converted to 3d vectors and vice
     * versa.
     * 
     * @param src
     *            the value of the source vector
     * @param dest
     *            the value of the destination vector
     */
    public static void convert(Vector3d src, Vector2d dest) {
        dest.x = src.x;
        dest.y = src.y;
    }

    /**
     * The <code>convert</code> methods have been overridden to allow 2d vectors to be converted to 3d vectors and vice
     * versa.
     * 
     * @param src
     *            the value of the source vector
     * @param dest
     *            the value of the destination vector
     */
    public static void convert(Vector2d src, Vector3d dest) {
        dest.x = src.x;
        dest.y = src.y;
        dest.z = 0;
    }

    /**
     * The <code>distance</code> method takes two vectors and computes their (Euclidean) distance. It has been
     * overloaded to allow the computation of the distance between a 3d vector and a 2d vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the distance between the two vectors
     */
    public static float distance(Vector3d a, Vector2d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return (float) Math.sqrt(dx * dx + dy * dy);
    }

    /**
     * The <code>distance</code> method takes two vectors and computes their (Euclidean) distance. It has been
     * overloaded to allow the computation of the distance between a 3d vector and a 2d vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the distance between the two vectors
     */
    public static float distance(Vector2d a, Vector3d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return (float) Math.sqrt(dx * dx + dy * dy);
    }

    /**
     * The <code>sqDistance</code> method takes two vectors and computes the square of their (Euclidean) distance. This
     * is just an optimization for the <code>distance</code> method that avoids an expensive floating point square root
     * computation. It has been overloaded to allow the computation of the distance between a 3d vector and a 2d vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the square of the distance between the two vectors
     */
    public static float sqDistance(Vector3d a, Vector2d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return dx * dx + dy * dy;
    }

    /**
     * The <code>sqDistance</code> method takes two vectors and computes the square of their (Euclidean) distance. This
     * is just an optimization for the <code>distance</code> method that avoids an expensive floating point square root
     * computation. It has been overloaded to allow the computation of the distance between a 3d vector and a 2d vector.
     * 
     * @param a
     *            the value of the first vector
     * @param b
     *            the value of the second vector
     * @returns the square of the distance between the two vectors
     */
    public static float sqDistance(Vector2d a, Vector3d b) {
        float dx = a.x - b.x;
        float dy = a.y - b.y;
        return dx * dx + dy * dy;
    }

}
