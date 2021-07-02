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

public class B extends A{

    public int i=1;

    /*@ public normal_behavior
      @  ensures \result==true;
      @*/
    public boolean test(){
	A a = new B();
	A.InnerA ia = a.new InnerA();
	InnerB ib = new InnerB(a);
	return ia.m()==ib.m() && ia.m()==0 && ib.n()==i;
    }

    class InnerB extends A.InnerA{
	
	public InnerB(A a){
	    a.super();
	}

	/*@ public normal_behavior
	  @  ensures \result==B.this.i;
	  @*/
	public int n(){
	    return i;
	}

    }

}
