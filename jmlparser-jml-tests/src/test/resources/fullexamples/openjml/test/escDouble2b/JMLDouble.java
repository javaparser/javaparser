// @(#)$Id: JMLDouble.java,v 1.34 2007/02/08 14:05:50 leavens Exp $

// Copyright (C) 2005 Iowa State University
//
// This file is part of the runtime library of the Java Modeling Language.
//
// This library is free software; you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation; either version 2.1,
// of the License, or (at your option) any later version.
//
// This library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with JML; see the file LesserGPL.txt.  If not, write to the Free
// Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA
// 02110-1301  USA.

/** A reflection of {@link java.lang.Double} that implements {@link JMLType}.
 *
 * @version $Revision: 1.34 $
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author David Cok
 * @see java.lang.Double
 * @see JMLDouble
 */
//-@ immutable
public /*@ pure @*/ strictfp class JMLDouble implements JMLComparable {

    /** The double that is the abstract value of this object.
     */
    //@ model public double theDouble;

    /*@ spec_public @*/ private double doubleValue;
    //@                                   in theDouble;
    //@ public represents theDouble = doubleValue;

    //@ public invariant owner == null;

    /** Initialize this object to contain zero.
     */
    /*@ public normal_behavior
      @   ensures theDouble == 0.0d;
      @ pure
      @*/
    public JMLDouble ( ) {
        doubleValue = 0.0d;
        //@ set owner = null;
    } 
   
    /** Initialize this object to contain the given double.
     */
    /*@   public normal_behavior
      @     requires !Double.isNaN(inDouble);
      @     ensures doubleValue == inDouble;
      @ also
      @   public normal_behavior
      @     requires Double.isNaN(inDouble);
      @     ensures Double.isNaN(theDouble);
      @ pure
      @*/ 
    public JMLDouble (double inDouble) {
        doubleValue = inDouble;
        //@ set owner = null;
    } 

    /** Initialize this object to contain an approximation to the
     * given integer.
     */
    /*@ public normal_behavior
      @   ensures theDouble == (double)inInt;
      @ pure
      @*/
    public JMLDouble (int inInt) {
        doubleValue = (double)inInt;
        //@ set owner = null;
    } 

    /** Initialize this object to contain the value of the given
     * Double.
     */
    /*@   public normal_behavior
      @     requires inDouble != null && !inDouble.isNaN();
      @     ensures theDouble == inDouble.theDouble;
      @ also
      @   public normal_behavior
      @     requires inDouble != null && inDouble.isNaN();
      @     ensures Double.isNaN(theDouble);
      @ pure
      @*/
    public JMLDouble(/*@ non_null */ Double inDouble) {
        doubleValue = inDouble.doubleValue();
        //@ set owner = null;
    }

    /** Initialize this object to contain the value given by the
     * string argument.
     */
    /*@ public normal_behavior
      @     requires Double.parseable(s);
      @     ensures Double.isFinite(theDouble);
      @     ensures Double.identical(doubleValue, Double.parseDouble(s));
      @     ensures Double.identical(doubleValue, new Double(s).doubleValue());
      @ also public exceptional_behavior
      @     requires !Double.parseable(s);
      @     signals_only NumberFormatException;
      @     signals (NumberFormatException) !Double.parseable(s);
      @ pure
      @*/
    public JMLDouble (/*@ non_null @*/ String s) throws NumberFormatException {
        doubleValue = new Double(s).doubleValue();
        //@ set owner = null;
    }

    /** Tell if this object contains either positive or negative infinity.
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theDouble == Double.POSITIVE_INFINITY) 
      @                   || (theDouble == Double.NEGATIVE_INFINITY);
      @*/
    public boolean isInfinite() {
  	return (doubleValue == Double.POSITIVE_INFINITY)
            || (doubleValue == Double.NEGATIVE_INFINITY);
    }

    /** Tell if this object contains NaN (not a number).
     */
    /*@ public normal_behavior
    @   ensures \result <==> Double.isNaN(theDouble); 
    @*/
    public boolean isNaN() {
	    return Double.isNaN(doubleValue);
    }

    /*@ public normal_behavior
      @   ensures \result <==> Double.isFinite(theDouble); 
      @*/
    public boolean isFinite() {
      return Double.isFinite(doubleValue);
    }

    /** Return a clone of this object.
     */
    /*@ also
      @   public normal_behavior
      @     requires !Double.isNaN(theDouble);
      @     ensures \result != null && \result instanceof JMLDouble 
      @             && Double.identical(((JMLDouble)\result).theDouble, theDouble); 
      @ also
      @   public normal_behavior
      @     requires Double.isNaN(theDouble);
      @     ensures \result != null && \result instanceof JMLDouble 
      @             && ((JMLDouble)\result).isNaN();
      @*/
    public Object clone() {
        return new JMLDouble(this.doubleValue);
    }
   
    /** Compare this to op2, returning a comparison code.
     *  @param op2 the object this is compared to.
     *  @exception ClassCastException when o is not a JMLDouble.
     */
    public int compareTo(/*@ non_null @*/ JMLComparable op2) throws ClassCastException {
    	//@ assume (op2 instanceof JMLDouble) <==> (\typeof(op2) <: \typeof(this));
    	if (!(op2 instanceof JMLDouble)) throw new ClassCastException();
        return Double.valueOf(doubleValue)
            .compareTo(Double.valueOf(((JMLDouble)op2).doubleValue));
    }

    /** Tell if the argument is zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   requires !Double.isNaN(d);
      @   ensures \result <==> (d == +0.0d || d == -0.0d);
      @*/
    public static /*@ pure @*/ boolean isZero(double d) {
        return d == +0.0d || d == -0.0d;
    }
  
    /** Tell if this object contains zero (either positive or negative).
     */
    /*@ public normal_behavior
      @   ensures \result <==> (theDouble == +0.0d || theDouble == -0.0d);
      @*/
    //@ helper
    public boolean isZero() {
        return doubleValue == +0.0d || doubleValue == -0.0d;
    }

    /** Tell whether this object is equal to the argument.
     */
    /*@ also
      @   public normal_behavior
      @     requires (op2 instanceof JMLDouble);
      @     old JMLDouble d = (JMLDouble)op2;
      @     requires \invariant_for(d);
      @     ensures !isNaN() && !d.isNaN() ==> \result == (theDouble == d.theDouble);
      @ also
      @   public normal_behavior
      @     requires !(op2 instanceof JMLDouble);
      @     ensures \result <==> false;
      @*/
    public boolean equals(/*@ nullable @*/ Object op2) {
        if (!(op2 instanceof JMLDouble)) {
            return false;
        }
        JMLDouble jmld2 = (JMLDouble)op2;
        // @ assert \invariant_for(jmld2);  // FIXME - why does this not prove, given the preconditions
        //@ assume \invariant_for(jmld2);
        if (isNaN() && jmld2.isNaN()) {
            return true;
        } else if (isZero() && jmld2.isZero()) {
            return true;
        } else if (!isNaN() && !jmld2.isNaN()) {
            double dv2 = jmld2.doubleValue;
            return doubleValue == dv2;
        } else {
        	return false;
        }
    } 

    /** Return a hash code for this object.
     */
    public int hashCode() {
        return new Double(doubleValue).hashCode();
    }

    /** Return the double contained in this object.
     */
    /*@ public normal_behavior
      @   requires !isNaN();
      @   ensures \result == doubleValue;
      @ also public normal_behavior
      @   requires isNaN();
      @   ensures Double.isNaN(\result);
      @*/
    public double doubleValue() {
        return doubleValue;
    }

    /** Return a Double containing the double contained in this object.
     */
    /*@ public normal_behavior
      @   ensures \result != null;
      @   ensures Double.identical(theDouble, \result.doubleValue());
      @*/
    public /*@ non_null @*/ Double getDouble() {
        return new Double(doubleValue);
    }

    /** Return the negation of this.
     */
    /*@ public normal_behavior
      @   requires !isNaN() && !Double.isNaN(-this.theDouble);
      @   ensures \result != null;
      @   ensures \result.theDouble == -this.theDouble;
      @*/
    public /*@ non_null @*/ JMLDouble negated() {
    	double x = -doubleValue;
        return new JMLDouble(-doubleValue);
    }

    /** Return the sum of this and the given argument.
     */
    /*@ public normal_behavior
      @   requires isFinite() && d2.isFinite() && !Double.isNaN(theDouble + d2.theDouble);
      @   ensures \result != null;
      @   ensures Double.identical(\result.theDouble, theDouble + d2.theDouble);
      @*/
    public /*@ non_null @*/ JMLDouble plus(/*@ non_null */ JMLDouble d2) {
        return new JMLDouble(doubleValue + d2.doubleValue);
    }

    /** Return the difference between this and the given argument.
     */
    /*@ public normal_behavior
      @   requires isFinite() && d2.isFinite() && !Double.isNaN(theDouble - d2.theDouble);
      @    //ensures \result != null;
      @    ensures Double.identical(\result.theDouble, theDouble - d2.theDouble);
      @*/
    public /*@ non_null @*/ JMLDouble minus(/*@ non_null */ JMLDouble d2) {
        return new JMLDouble(doubleValue - d2.doubleValue);
    }

    /** Return the product of this and the given argument.
     */
    /*@ public normal_behavior
      @   requires isFinite() && d2.isFinite() && !Double.isNaN(theDouble * d2.theDouble);
      @    ensures \result != null;
      @      ensures \result.theDouble == theDouble * d2.theDouble;
      @*/
    public /*@ non_null @*/ JMLDouble times(/*@ non_null */ JMLDouble d2) {
        return new JMLDouble(doubleValue * d2.doubleValue);
    }

    /** Return the quotient of this divided by the given argument.
     */
    /*@ public normal_behavior
      @     requires isFinite() && d2.isFinite();
      @      requires d2.theDouble != 0 && !Double.isNaN(theDouble / d2.theDouble);
      @      ensures \result.theDouble == theDouble / d2.theDouble;
      @*/
    public /*@ non_null @*/
        JMLDouble dividedBy(/*@ non_null */ JMLDouble d2) {
        return new JMLDouble(doubleValue / d2.doubleValue);
    }

    /** Return the remainder of this divided by the given argument.
     */
    /*@ public normal_behavior
      @   requires isFinite() && d2.isFinite() && !Double.isNaN(theDouble % d2.theDouble);
      @      requires d2.theDouble != 0.0;
      @      ensures \result.theDouble == theDouble % d2.theDouble;
      @*/
    public /*@ non_null @*/
        JMLDouble remainderBy(/*@ non_null @*/ JMLDouble d2) {
        JMLDouble r = new JMLDouble(doubleValue % d2.doubleValue());
        //@ show this, d2, r, this.theDouble, d2.theDouble, r.theDouble;
        return r;
    }

    /** Tell whether this is strictly greater than the given argument.
     */
    /*@ public normal_behavior
      @   requires !isNaN() && !d2.isNaN();
      @   ensures \result <==> this.theDouble > d2.theDouble;
      @*/
    public boolean greaterThan(/*@ non_null */ JMLDouble d2) {
        return (doubleValue > d2.doubleValue());
    }

    /** Tell whether this is strictly less than the given argument.
     */
    /*@ public normal_behavior
      @   requires !isNaN() && !d2.isNaN();
      @   ensures \result <==> this.theDouble < d2.theDouble;
      @*/
    public boolean lessThan(/*@ non_null */ JMLDouble d2) {
        return (doubleValue < d2.doubleValue());
    }

    /** Tell whether this is greater than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires !isNaN() && !d2.isNaN();
      @   ensures \result <==> this.theDouble >= d2.theDouble;
      @*/
    public boolean greaterThanOrEqualTo(/*@ non_null */ JMLDouble d2) {
        return (doubleValue >= d2.doubleValue());
    }

    /** Tell whether this is less than or equal to the given argument.
     */
    /*@ public normal_behavior
      @   requires !isNaN() && !d2.isNaN();
      @   ensures \result <==> this.theDouble <= d2.theDouble;
      @*/
    public boolean lessThanOrEqualTo(/*@ non_null */ JMLDouble d2) {
        return (doubleValue <= d2.doubleValue());
    }
    
    /** Return a string representation of this object.
     */
    // specification inherited from Object
    public String toString() {
        return String.valueOf(doubleValue);
    }

    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d2 != null && !Double.isNaN(theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==> 
      @             StrictMath.abs(theDouble - d2.theDouble) <= epsilon;
      @*/
    public boolean withinEpsilonOf(/*@ non_null @*/ JMLDouble d2,
                                   double epsilon) {
        return StrictMath.abs(doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d2 != null && !Double.isNaN(theDouble - d2.theDouble);
      @    requires !Double.isNaN(StrictMath.max(StrictMath.abs(theDouble), StrictMath.abs(d2.theDouble)) * epsilon);
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2.theDouble, epsilon);
      @*/
    public boolean approximatelyEqualTo(/*@ non_null @*/ JMLDouble d2,
                                        double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2.doubleValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d2 != null && !Double.isNaN(theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==> 
      @             (StrictMath.abs(theDouble - d2.doubleValue()) <= epsilon);
      @*/
    public boolean withinEpsilonOf(/*@ non_null @*/ Double d2,
                                   double epsilon) {
        return StrictMath.abs(doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d2 != null && !Double.isNaN(theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(theDouble - d2.theDouble);
      @    requires !Double.isNaN(StrictMath.max(StrictMath.abs(theDouble), StrictMath.abs(d2.theDouble)) * epsilon);
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2.doubleValue(), epsilon);
      @*/
    public boolean approximatelyEqualTo(/*@ non_null @*/ Double d2,
                                        double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2.doubleValue(), epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires !isNaN() && !Double.isNaN(d2) && !Double.isNaN(theDouble - d2) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(theDouble - d2) <= epsilon;
      @*/
    public boolean withinEpsilonOf(double d2, double epsilon) {
        return StrictMath.abs(doubleValue()-d2) <= epsilon;
    }

    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires !isNaN() && !Double.isNaN(d2) && !Double.isNaN(theDouble - d2) && !Double.isNaN(epsilon);
      @    requires !Double.isNaN(StrictMath.max(StrictMath.abs(this.doubleValue), StrictMath.abs(d2)) * epsilon);
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(theDouble, d2, epsilon);
      @*/
    public boolean approximatelyEqualTo(double d2, double epsilon) {
        return approximatelyEqualTo(doubleValue(), d2, epsilon);
    }    
    
    /** Tell whether absolute value of difference of the two arguments
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires !Double.isNaN(d1) && !Double.isNaN(d2) && !Double.isNaN(d1 - d2) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(d1 - d2) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(double d1, double d2,
                                                         double epsilon)
    {
        return StrictMath.abs(d1-d2) <= epsilon;
    }

    /** Tell whether relative difference of the two arguments is 
     *   within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires !Double.isNaN(d1) && !Double.isNaN(d2) && !Double.isNaN(d1 - d2) && !Double.isNaN(epsilon);
      @    requires !Double.isNaN(StrictMath.max(StrictMath.abs(d1), StrictMath.abs(d2)) * epsilon);
      @    assignable \nothing;
      @    ensures \result <==>
      @      d1 == d2
      @      || StrictMath.abs(d1 - d2)
      @            <= StrictMath.max(StrictMath.abs(d1),
      @                              StrictMath.abs(d2))
      @               * epsilon;
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
        double d1, double d2, double epsilon)
    {
        return d1 == d2
            || StrictMath.abs(d1-d2)
               <= StrictMath.max(StrictMath.abs(d1),
                                 StrictMath.abs(d2))
                  * epsilon;
    }    

    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(d1.theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==> 
      @             StrictMath.abs(d1.theDouble - d2.theDouble) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLDouble d1,
                                          /*@ non_null @*/ JMLDouble d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(d1.theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    requires !Double.isNaN(StrictMath.max(StrictMath.abs(d1.theDouble), StrictMath.abs(d2.theDouble)) * epsilon);
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(d1.theDouble, d2.theDouble, epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLDouble d1,
                                               /*@ non_null @*/ JMLDouble d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2.doubleValue(),
                                    epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(d1.theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    requires d1 != null && d2 != null;
      @    assignable \nothing;
      @    ensures \result <==>
      @         StrictMath.abs(d1.theDouble - d2.doubleValue()) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLDouble d1,
                                          /*@ non_null @*/ Double d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2.doubleValue()) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null && d2 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2.theDouble) && !Double.isNaN(d1.theDouble - d2.theDouble) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result
      @     <==> approximatelyEqualTo(d1.theDouble, d2.doubleValue(), epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLDouble d1,
                                               /*@ non_null @*/ Double d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2.doubleValue(),
                                    epsilon);
    }
    
    /** Tell whether absolute value of difference of this JMLDouble and the arg
     *  is within the given epsilon.
     */
    /*@ public normal_behavior
      @    requires d1 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2) && !Double.isNaN(d1.theDouble - d2) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result <==> StrictMath.abs(d1.theDouble - d2) <= epsilon;
      @*/
    public static /*@ pure @*/ boolean withinEpsilonOf(
                                          /*@ non_null @*/ JMLDouble d1,
                                          double d2,
                                          double epsilon) {
        return StrictMath.abs(d1.doubleValue()-d2) <= epsilon;
    }
    
    /** Tell whether relative difference of this JMLDouble and the arg is 
     *   within the given epsilon.
     *  @see #approximatelyEqualTo(double, double, double)
     */
    /*@ public normal_behavior
      @    requires d1 != null && !Double.isNaN(d1.theDouble) && !Double.isNaN(d2) && !Double.isNaN(d1.theDouble - d2) && !Double.isNaN(epsilon);
      @    assignable \nothing;
      @    ensures \result
      @       <==> approximatelyEqualTo(d1.theDouble, d2, epsilon);
      @*/
    public static /*@ pure @*/ boolean approximatelyEqualTo(
                                               /*@ non_null @*/ JMLDouble d1,
                                               double d2,
                                               double epsilon) {
        return approximatelyEqualTo(d1.doubleValue(), d2, epsilon);
    }
}
