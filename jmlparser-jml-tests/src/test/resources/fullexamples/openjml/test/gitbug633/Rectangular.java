// @(#)$Id: Rectangular.java 1199 2009-02-17 19:42:32Z smshaner $

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

/** Complex numbers in rectangular coordinates.
 * @author Gary T. Leavens with help from Abelson and Sussman's
 *          <cite>Structure and Interpretation of Computer Programs</cite>
 */
public /*@ pure @*/ strictfp class Rectangular extends ComplexOps {

    /** The real part of this number. */
    private double re;
    /** The imaginary part of this number. */
    private double img;
    
    /** Initialize this Complex number to be 0+(0*i). */
    //@ ensures realPart() == 0.0 && imaginaryPart() == 0.0;
    public Rectangular() {
        this(0.0);
    }    

    /** Initialize this Complex number to be re+(0*i). */
    /*@   requires !Double.isNaN(re);
      @   ensures realPart() == re && imaginaryPart() == 0.0;
      @ also
      @   requires Double.isNaN(re);
      @   ensures Double.isNaN(realPart()) && imaginaryPart() == 0.0;
      @*/
    public Rectangular(double re) {
        this(re, 0);
    }
    
    /** Initialize this Complex number to be re+(img*i). */
    /*@
      @ ensures !Double.isNaN(re) ==> realPart() == re;
      @ ensures !Double.isNaN(img) ==> imaginaryPart() == img;
      @ ensures Double.isNaN(re) ==> Double.isNaN(realPart());
      @ ensures Double.isNaN(img) ==> Double.isNaN(imaginaryPart());
      @*/
    public Rectangular(double re, double img) {
        this.re = re;
        this.img = img;
    }

    // specification inherited
    public double realPart() {
        return re;
    }

    // specification inherited
    public double imaginaryPart() {
        return img;
    }

    // specification inherited
    public double magnitude() {
        return StrictMath.sqrt(re*re + img*img);
    }

    // specification inherited
    public double angle() {
        return StrictMath.atan2(img, re);
    }

    // specification inherited
    public String toString() {
        return re + " + " + img + "*i";
    }
}
