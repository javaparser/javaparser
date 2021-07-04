// @(#)$Id: Polar.java 1199 2009-02-17 19:42:32Z smshaner $

// Copyright (C) 2003 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package org.jmlspecs.samples.dbc;

/** Complex numbers in polar coordinates.
 * @author Gary T. Leavens with help from Abelson and Sussman's
 *          <cite>Structure and Interpretation of Computer Programs</cite>
 */
public /*@ pure @*/ strictfp class Polar extends ComplexOps {
    
    /** The magnitude of this number. */
    private double mag;
    /** The angle of this number. */
    private double ang;
    
    /** Initialize this polar coordinate number
     * with magnitude mag and angle ang, except that
     * when the magnitude is negative, this
     * is interpreted as magnitude -mag and angle ang+StrictMath.PI.
     * @param mag the magnitude desired
     * @param ang the angle in radians, measured
     *            counterclockwise from the positive x axis
     */
    /*@   requires mag >= 0 && Double.NEGATIVE_INFINITY < ang
      @         && ang < Double.POSITIVE_INFINITY;
      @   ensures this.magnitude() == mag;
      @   ensures this.angle() == standardizeAngle(ang);
      @ also
      @   requires mag < 0 && Double.NEGATIVE_INFINITY < ang
      @         && ang < Double.POSITIVE_INFINITY;
      @   ensures this.magnitude() == - mag;
      @   ensures this.angle() == standardizeAngle(ang+StrictMath.PI);
      @ also
      @   requires Double.isNaN(mag) || Double.isNaN(ang)
      @            || Double.NEGATIVE_INFINITY == ang
      @            || ang == Double.POSITIVE_INFINITY;
      @   signals_only IllegalArgumentException;
      @*/
    public Polar(double mag, double ang)
        throws IllegalArgumentException
    {
        if (Double.isNaN(mag)) {
            throw new IllegalArgumentException();
        }
        if (mag < 0) {
            mag = -mag;
            ang += StrictMath.PI;
        }
        this.mag = mag;
        this.ang = standardizeAngle(ang);
    }

    /** Standardize the angle so it's between
     * -StrictMath.PI and StrictMath.PI (radians).
     */
    /*@   requires Double.NEGATIVE_INFINITY < rad
      @            && rad < Double.POSITIVE_INFINITY;
      @   ensures -StrictMath.PI <= \result && \result <= StrictMath.PI;
      @ also
      @   requires Double.isNaN(rad) || Double.NEGATIVE_INFINITY == rad
      @            || rad == Double.POSITIVE_INFINITY;
      @   signals_only IllegalArgumentException;
      @*/
    public static /*@ pure @*/ double standardizeAngle(double rad)
        throws IllegalArgumentException
    {
        if (Double.isNaN(rad) || rad == Double.NEGATIVE_INFINITY 
            || rad == Double.POSITIVE_INFINITY) {
            throw new IllegalArgumentException();
        }
        rad = rad % (2*StrictMath.PI);
        if (rad > StrictMath.PI) {
            return rad - 2*StrictMath.PI;
        } else if (rad < -StrictMath.PI) {
            return rad + 2*StrictMath.PI;
        } else {
            return rad;
        }
    }

    // specification inherited
    public double realPart() {
        return mag * StrictMath.cos(ang);
    }

    // specification inherited
    public double imaginaryPart() {
        return mag * StrictMath.sin(ang);
    }

    // specification inherited
    public double magnitude() {
        return mag;
    }

    // specification inherited
    public double angle() {
        return ang;
    }

    // specification inherited
    public String toString() {
        return "(" + mag + ", " + ang + ")";
    }
}
