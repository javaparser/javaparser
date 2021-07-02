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

class AbruptTermination {
   int[] ia;
    /* @ normalbehavior
       @           requires ia != null ;
       @       assignable ia[];
       @             ensures \forall int i; 0<=i && i<ia.length ==>
       @                   (\old ( ia[i]) < 0 &&
       @                   ( // i is the first position with negative value
       @                     \forall int j; 0 <= j && j<i ==> \old(ia[j]) >= 0 ) )
       @                   ? ( ia[i] == -\old ( ia[i] ) )
       @                   : ( ia[i] == \old ( ia[i] ) ) ;
       @ */

   void negatefirst() {
       /* @ maintaining i >= 0 &&  i < = ia.length &&
	  @ ( \forall int j; 0<=j && j<i ==>
	  @
	  @ ( ia[j] >= 0 && ia[j] == \old ( ia [j] ) ) ) ;
	  @ decreasing ia.length - i ;
	  @*/
         for (int i = 0 ; i < ia.length; i++) {
                 if ( ia[i] < 0 ) { ia [i] = -ia[i] ; 
		     break ; 
		 } 
	 }
   }
}
