// example from page 151
// shows that keeping the context in the second and third premiss
// of the invariant rule is not sound. Keeping the context can be simulated
// by providing an empty modifier set for the loop (see the JML annotation in 
// the source code). 

class KeepingContextIsUnsound {

    /*@ public normal_behavior
      @  requires i==0;
      @  ensures \result==0;
      @  diverges true; 
      @*/
    int dummy(int i) {	
	/*@ loop_invariant true;
	  @ assignable \nothing;
	  @*/
	while ( i<10 ) { 
	    i=i+1; 
	}
	return i;
    }

}


