// @(#)$Id: JMLType.java,v 1.20 2006/08/16 17:40:34 leavens Exp $

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


/** Objects with a clone and equals method.
 * JMLObjectType and JMLValueType are refinements
 * for object and value containers (respectively).
 * @version $Revision: 1.20 $
 * @author Gary T. Leavens and Albert L. Baker.
 * @see JMLObjectType
 * @see JMLValueType
 */
//@ pure
public interface JMLType extends Cloneable, java.io.Serializable {

    /** Return a clone of this object. */
    /*@  public normal_behavior
      @     ensures \result != null;
      @     ensures \result instanceof JMLType;
      @     ensures ((JMLType)\result).equals(this);
      @*/
    //@ implies_that
    /*@    ensures \result != null
      @        && \typeof(\result) <: \type(JMLType);
      @*/
    public /*@ pure @*/ Object clone();    

    /** Test whether this object's value is equal to the given argument.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result ==>
      @             ob2 != null
      @             && (* ob2 is not distinguishable from this,
      @                   except by using mutation or == *);
      @ implies_that
      @   public normal_behavior
      @   {|
      @      requires ob2 != null && ob2 instanceof JMLType;
      @      ensures ((JMLType)ob2).equals(this) == \result;
      @    also
      @      requires ob2 == this;
      @      ensures \result <==> true;
      @   |}
      @*/
    public /*@ pure @*/ boolean equals(/*@ nullable @*/ Object ob2);    

    /** Return a hash code for this object. */
    public /*@ pure @*/ int hashCode();
}
