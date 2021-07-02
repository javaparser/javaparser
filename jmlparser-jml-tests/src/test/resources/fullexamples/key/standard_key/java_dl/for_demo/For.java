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

class For {

    /* This method should be proven automatically since the contract
     * of the for loop is transferred to the generated while loop
     */

    /*@ requires length > 0;
      @ ensures \result == length;
      @*/
    public int annotations(int length) {
	int count = 0;

	/*@ loop_invariant i >= 0 & i <= length & count == i;
	  @ decreasing length - i;
          @ assignable count, i;
	  @*/
	for(int i = 0; i < length; i++) {
	    count = count + 1;
	}

	return count;
    }

    
    /* 
     * This method should be proven automatically since the contract
     * of the for loop is transferred to the generated while loop
     */

    /*@ requires array != null && array.length > 0;
      @ ensures (\forall int i; i >= 0 && i < \old(array).length; \result <= \old(array)[i]);
      @ ensures (\forall int i; i >= 0 && i < \old(array).length; array[i] == \old(array)[i]);
    */
    public int array_min(int[] array) {

	int min = array[0];

	/*@ loop_invariant (\forall int j; j >= 0 && j < i; min <= array[j]);
	  @ assignable i, min;
	  @ decreasing array.length - i;
	*/
	for(int i = 1; i < array.length; i++) {
	    if(min > array[i])
		min = array[i];
	}

	return min;
    }

    
    /*
     * This method is used to show that loops are treated correctly
     * even if parts are left out.
     */

    /*@ requires true;
      @ ensures true;
    */
    public void leave_out() {

	for(int i = 0; i < 100;) { break; }
	for(int i = 0; ;i++) { break; }
	for(;;) { break; }
    
    }


    /*
     * This method checks whether breaks and continues are handled
     * correctly.
     */

    /*@ requires true;
      @ ensures \result;
    */
    public boolean checkBreakContinue() {
	int dummy;
	boolean ret = true;

	outerlabel: {
	    dummy = 0;  // some statement
	    for(;dummy == 0;dummy++) {
		break outerlabel;
	    }
	}

	// dummy must be 0 here
	ret &= (dummy == 0);

	dummy = 0;
	for(; dummy == 0; dummy++) {
	    break;
	}
	// dummy must be 0 here
	ret &= (dummy == 0);
	
	dummy = 0;
	for(; dummy == 0; dummy++) {
	    continue;
	}
	// dummy must be 1 here
	ret &= (dummy == 1);

	dummy = 0;
	outer: while(dummy == 0) {
	    dummy = 1;
	    for(; true; dummy++) {
		continue outer;
	    }
	}
	// dummy must be 1 here
	ret &= (dummy == 1);

	return ret;

    }
}
