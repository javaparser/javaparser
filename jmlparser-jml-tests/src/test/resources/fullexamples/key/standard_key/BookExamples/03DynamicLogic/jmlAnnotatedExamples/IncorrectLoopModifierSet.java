// example from page 159
// the example shows that a modifier set for the loop body is not a correct loop modifier set
// use as an invariant: ( self.a=0 | self.a=5 ) & 0<=i & i<=10
// use as _INCORRECT_ modifier set: { i, \if (i>0) self.a}
// as the KeY book was printed the loop invariant rule did not yet check for 
// the correctness of assignable clauses; this has changed, so the example will not close any longer
// will not clsoe any longer as KeY checks now for validity of the loop assignable clause
// the goal left open is the one checking for its correctness, but you can see that all other parts
// are actually valid when having a wrong assignable clause

class IncorrectLoopModifierSet {

    int a;

    /*@ public normal_behavior
      @  requires i==0 && a==0;
      @  ensures a==0;
      @  diverges true; 
      @*/
    void dummy(int i) {	
	while ( i<10 ) {
	    if ( i>0 ) {
		a = 5;
	    }
	    i=i+1;
	}
    }
}
