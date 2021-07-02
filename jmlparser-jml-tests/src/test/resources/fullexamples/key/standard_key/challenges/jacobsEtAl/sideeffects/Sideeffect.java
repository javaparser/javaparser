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

class Sideeffect {

    boolean b = true;
    boolean result1,result2;
    /* @normal_behavior
       @requires true;
       @assignable b;
       @ensures b==!\old(b) && \result==b;
       @
    */
    boolean f(){
	b = !b;
	return b;
    }
    
    /*@normal_behavior
      @         requires true ;
      @       assignable b , result1 , result2 ;
      @  ensures(\old(b)==>!result1 && result2)&&
      @ (!\old(b)==> result1 && result2);
      @*/
    void m () {    
	result1 = f() || !f() ; 
	result2 = !f() && f() ; 
    }    
}
