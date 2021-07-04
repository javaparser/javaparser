/* A simple linked list of entries. */
public class EntryList {
    /*@spec_public @*/ Object first;
    /*@spec_public @*/ EntryList rest;

    EntryList( Object first, EntryList rest) {
        this.first = first;
        this.rest = rest;
    }

    /*@ ensures (this.first == null ==> \result == 0);
      @ ensures (this.first != null && this.rest == null) ==> \result == 1;
      @ ensures (this.first != null && this.rest != null) ==> \result == (rest.size() + 1);
      @*/
    //@ pure
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

