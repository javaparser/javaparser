/* A simple linked list of entries. */  
// This is the original error report - the stack overflow stems from repeatedly inlining the size() call in the ensures clause
// Added the nullable and pure modifiers
public class EntryList {
    /*@spec_public nullable @*/ Object first;
    /*@spec_public nullable @*/ EntryList rest;

    EntryList( /*@ nullable */ Object first,  /*@ nullable */ EntryList rest) {
        this.first = first;
        this.rest = rest;
    }

    /*@ ensures (this.first == null && \result == 0) ||(this.rest == null && \result == 1)  ||
      @ (\result == rest.size() + 1);
      @ pure
      @*/
    public int size() {  //@ assume rest != null ==> rest.size() < 1000000000; // Just to avoid overflow warnings
        if(this.first == null) {
            return 0;
        }
        if(this.rest == null) {
            return 1;
        } else {
            return 1 + rest.size();
        }
    }
}

