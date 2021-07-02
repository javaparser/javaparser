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
    C a;
    int i ;
    /* @ normalbehavior
       @         requires true ;       
       @      assignable a, i ;
       @      ensures a==null && i==1;
       @*/
          C( ) { a = null ; i = 1 ; }
}


class Alias {
    /* @ normalbehavior
       @          requires true ;
       @      assignable \nothing;
       @            ensures \result == 4;
       @ */
    int m() {
	C c = new C ( ) ;
	c.a = c;
	c.i = 2;
	return c.i + c.a.i;
    }
}

