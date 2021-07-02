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

/**
 * This class can be used to test the inner classes mechanism
 */

class InnerClasses {

    private int privField = 0;
    
    class Innerst {

	Innerst(int val) {
	    // ignore argument
	}
	
	void setPrivField() {
	    privField = 1;
	}
    }


    void anonClass() {
	final int newValue = 2;

	Innerst anon = new Innerst(17) {
		void setPrivField() {
		    privField = newValue;
		}
	    };

	anon.setPrivField();
    }

/*  
    // for comparison only
    public static void main(String args[]) {
	InnerClasses ic = new InnerClasses();
	InnerClasses.Innerst i = ic.new Innerst(42);
	
	System.out.println("pre: " + ic.privField);

	i.setPrivField();
	System.out.println("post 1: " + ic.privField);

	ic.anonClass();
	System.out.println("post 2: " + ic.privField);
    }
*/

}
