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

// geht nich:  ensures \result == ((n > 100) ? (n - 10) : 91);

public class Function91 {
    /*@ public normal_behavior
      @ requires true;
      @ ensures ( (n > 100) ==> \result == n - 10 ) &&
                ( (n <= 100) ==> \result == 91 );
      @ assignable \nothing;
      @ diverges true;
      @*/
    public static int f ( int n ) {
	if (n > 100) return n - 10;
	else return f(f(n+11));
    }
}
