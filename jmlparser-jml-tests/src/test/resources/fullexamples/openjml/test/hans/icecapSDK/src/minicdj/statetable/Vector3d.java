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
package minicdj.statetable;

/**
 * The <code>Vector3d</code> class implements a 3-dimensional vector that can represent the position or velocity of an
 * object within a 3D space. This implementation uses public, non-final fields to avoid as much object creation as
 * possible. Java does not have value types per se, but these vector classes are the closest thing that is possible.
 * 
 * @author Ben L. Titzer
 */
/*@javax.safetycritical.annotate.Scope("cdx.Level0Safelet")*/
public final class Vector3d {
    public float x, y, z;

    /**
     * The default constructor for the <code>Vector3d</code> returns an object representing the zero vector.
     */
    public Vector3d() {}

    /**
     * The main constructor for the <code>Vector3d</code> class takes the three coordinates as parameters and produces
     * an object representing that vector.
     * 
     * @param x
     *            the coordinate on the x (east-west) axis
     * @param y
     *            the coordinate on the y (north-south) axis
     * @param z
     *            the coordinate on the z (elevation) axis
     */
    public Vector3d(float x, float y, float z) {
        this.x = x;
        this.y = y;
        this.z = z;
    }

    /**
     * The secondary constructor for the <code>Vector3d</code> class takes a vector to copy into this new instance and
     * returns an instance that represents a copy of that vector.
     * 
     * @param v
     *            the vale of the vector to copy into this new instance
     */
    public Vector3d(Vector3d v) {
        this.x = v.x;
        this.y = v.y;
        this.z = v.z;
    }

    /**
     * The <code>set</code> is basically a convenience method that resets the internal values of the coordinates.
     * 
     * @param x
     *            the coordinate on the x (east-west) axis
     * @param y
     *            the coordinate on the y (north-south) axis
     * @param z
     *            the coordinate on the z (elevation) axis
     */
    /*@javax.safetycritical.annotate.AllocFree*/
    public void set(float x, float y, float z) {
        this.x = x;
        this.y = y;
        this.z = z;
    }

    /**
     * The <code>set</code> is basically a convenience method that resets the internal values of the coordinates.
     * 
     * @param val
     *            the value of the vector
     */
    public void set(Vector3d val) {
        this.x = val.x;
        this.y = val.y;
        this.z = val.z;
    }

    /**
     * The <code>zero</code> method is a convenience method to zero the coordinates of the vector.
     */
    public void zero() {
        x = y = z = 0;
    }

    public boolean equals(Object o) {
        try {
            return equals((Vector3d) o);
        } catch (ClassCastException e) {
            return false;
        }
    }

    public boolean equals(Vector3d b) {
        if (x != b.x) return false;
        if (y != b.y) return false;
        if (z != b.z) return false;
        return true;
    }

    public int hashCode() {
        return (int) ((x + y + z) * y + (x - y + z) * x - (x - y - z) * z);
    }

    public String toString() {
        return "(" + x + ", " + y + ", " + z + ")";
    }
}
