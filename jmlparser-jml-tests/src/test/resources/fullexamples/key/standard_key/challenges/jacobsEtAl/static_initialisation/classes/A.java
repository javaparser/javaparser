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

class C {
    
    static boolean result1, result2, result3, result4;

    static void m() {
	result1 = C1.b1; result2 = C2.b2;
	result3 = C1.d1; result4 = C2.d2;
    }        
}

class C1 {
    static boolean b1 = C2.d2;
    static boolean d1 = true;
}

class C2 {
    static boolean d2 = true;
    static boolean b2 = C1.d1;
}
