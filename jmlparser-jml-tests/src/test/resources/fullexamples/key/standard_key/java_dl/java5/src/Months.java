// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/* 
   This example is referenced in the thesis on Java 5.

   The contract can be proven with 1267 nodes in 16 branches with
   one manual instantiation (expand dynamic types).
   
   Java does not recognize exhaustive matching in a switch statement
   so that the final throw statement is needed to avoid a missing- 
   return-statement error.
   
   KeY being aware of enum types can however prove that this
   exceptional case will never occur.

 */

enum Month { JAN, FEB, MAR, APR, MAY, JUN, JUL, AUG, SEP, OCT, NOV, DEC};


class Example {

    boolean leapYear;


    /*@ public normal_behavior 
      @   requires month != null;
      @   ensures \result > 0 && \result <= 31;
      @*/
    int daysInMoth(Month month) {
	switch(month) {
	case Month.JAN:
	case Month.MAR:
	case Month.MAY:
	case Month.JUL:
	case Month.AUG:
	case Month.OCT:
	case Month.DEC:
	    return 31;

	case Month.APR:
	case Month.JUN:
	case Month.SEP:
	case Month.NOV:
	    return 30;

	case Month.FEB:
	    return leapYear ? 29 : 28;
	}
	throw new Error();
    }

}
