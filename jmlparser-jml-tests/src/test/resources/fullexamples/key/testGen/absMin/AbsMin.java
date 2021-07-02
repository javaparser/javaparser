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

public class AbsMin{

    /*@ public normal_behavior
      @   ensures \result == ((a<b? a : b)<0 ? -(a<b? a : b) : (a<b? a : b));
      @*/
    public static int absMinErr(int a, int b){
	int result = b;
	if(a<b){
	    result = a;
	}
	if(result<0){
	    result = -result;
	}
	return -result;
    }

    /*@ public normal_behavior
      @   ensures \result == ((a<b? a : b)<0 ? -(a<b? a : b) : (a<b? a : b));
      @*/
    public static int absMin(int a, int b){
	int result = b;
	if(a<b){
	    result = a;
	}
	if(result<0){
	    result = -result;
	}
	return result;
    }

}
