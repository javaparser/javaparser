// @(#)$Id: ComplexOps.java 1199 2009-02-17 19:42:32Z smshaner $

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

/** An abstract class that holds all of the common algorithms for
 *  complex numbers.  Note that this class knows about both of its subclasses
 *  Rectangular and Polar.
 *
 *  @author Gary T. Leavens with help from Abelson and Sussman's
 *          <cite>Structure and Interpretation of Computer Programs</cite>
 */
public /*@ pure @*/ strictfp abstract class ComplexOps implements Complex {

    // specification inherited
    public Complex add(Complex b) {
        return new Rectangular(this.realPart() + b.realPart(),
                               this.imaginaryPart() + b.imaginaryPart());
    }

    // specification inherited
    public Complex sub(Complex b) {
        return new Rectangular(this.realPart() - b.realPart(),
                               this.imaginaryPart() - b.imaginaryPart());
    }

    // specification inherited
    public Complex mul(Complex b) {
        try {
            return new Polar(this.magnitude() * b.magnitude(),
                             this.angle() + b.angle());
        } catch (IllegalArgumentException e) {
            return new Rectangular(Double.NaN);
        }
    }

    // specification inherited
    public Complex div(Complex b) {
        try {
            return new Polar(this.magnitude() / b.magnitude(),
                             this.angle() - b.angle());
        } catch (IllegalArgumentException e) {
            return new Rectangular(Double.NaN);
        }
    }
    
    // specification inherited
    public boolean equals(/*@ nullable @*/ Object o) {
        if (!(o instanceof Complex)) {
            return false;
        }
        Complex b = (Complex) o;
        return this.realPart() == b.realPart()
                && this.imaginaryPart() == b.imaginaryPart();
    }
    
    // specification inherited
    public int hashCode() {
        return (int) (this.realPart() + this.imaginaryPart());
    }

}
