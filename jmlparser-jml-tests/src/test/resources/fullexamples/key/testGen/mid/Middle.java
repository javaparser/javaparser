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

public class Middle{

    /*@ public normal_behavior
      @  ensures \result==x || \result==y || \result==z;
      @  ensures \result<=y && \result<=z || \result<=x && \result<=z ||
      @          \result<=x && \result<=y;
      @  ensures \result>=y && \result>=z || \result>=x && \result>=z ||
      @          \result>=x && \result>=y;
      @*/
    public static int middle(int x, int y, int z){
	int mid = z;
	if(y<z){
	    if(x<y){
		mid = y;
	    }else if(x<z){
		mid = x;
	    }
	}else{
	    if(x>y){
		mid = y;
	    }else if(x>z){
		mid = x;
	    }
	}
	return mid;
    }

}
