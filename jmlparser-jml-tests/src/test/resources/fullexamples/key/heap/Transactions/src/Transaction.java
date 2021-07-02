final class Transaction {
    int amount;
    /*@nullable*/ Transaction next;

    //@ ghost int total;
    //@ ghost int id;
    //@ ghost \locset footprint;
    /*@ public invariant footprint == \set_union(\all_fields(this), 
         (this.next == null) ? \empty : this.next.footprint);
    */

    /* @ public invariant footprint ==              
             \set_union(\singleton(this.footprint),
             \set_union(\singleton(this.amount), 
             \set_union(\singleton(this.id),
             \set_union(\singleton(this.next),
             \set_union(\singleton(this.total),
             (next==null) ? \empty : next.footprint)))));
    */
    
    /*@ public invariant 
          \subset(footprint, (\infinite_union Transaction t; t.*));
    */

    //@ invariant id >= 0;
    //@ invariant total == amount + ((next == null) ? 0 : next.total);
    /*@ invariant next == null || 
         (id > next.id && 
          next.\inv && 
          \disjoint(this.*, next.footprint));
    */

    //@ accessible \inv: footprint \measured_by id;

    /*@ requires next == null || next.\inv;
      @ ensures this.next == next && this.amount == amount &&
      @   total == amount + ((next == null) ? 0 : next.total);
      @ modifies \nothing;
      @*/
    Transaction(/*@nullable*/ Transaction next, int amount) {
        this.next = next;
        this.amount = amount;
        //@ set this.total = amount + ((next == null) ? 0 : next.total);
        //@ set this.id = (next == null) ? 0 : next.id + 1;
        /*@ set this.footprint =
             \set_union(\all_fields(this), 
             (next == null) ? \empty : next.footprint);
        */
        //      while(false);
    }

    /*@ requires true;
      @ ensures \result == total;
      @ modifies \nothing;
      @ measured_by this.id;
      @*/
    int getTotal() {
        if(next == null) {
            return amount;
        } else {
            return next.getTotal() + amount;
        }
    }
        
}
