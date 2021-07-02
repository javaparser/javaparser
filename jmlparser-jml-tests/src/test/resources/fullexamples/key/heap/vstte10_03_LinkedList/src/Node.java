class Node {   
    private int head;
    private /*@nullable@*/ Node next;
    
    //@ public ghost \seq seq;
    //@ public ghost \locset repr;

    
    /*@ private invariant \subset(this.*, repr) && 1 <= seq.length && seq[0] == head;
      @ private invariant next == null ==> seq.length == 1;
      @ private invariant next != null ==> \subset(next.*, repr)
      @                                    && \subset(next.repr, repr)
      @                                    && \disjoint(this.*, next.repr)
      @                                    && seq[1..seq.length] == next.seq
      @                                    && \invariant_for(next);
      @*/
       
    //@ accessible \inv: repr \measured_by seq.length;


    /*@ public normal_behaviour
      @   requires tail == null || \invariant_for(tail);
      @   ensures \invariant_for(\result);
      @   ensures tail == null ==> \result.seq == \seq_singleton(x);
      @   ensures tail != null ==> \result.seq == \seq_concat(\seq_singleton(x), tail.seq);
      @*/
    public static /*@pure@*/ Node cons(int x, /*@nullable@*/ Node tail) { 
	Node n = new Node();
    	n.head = x;
    	n.next = tail;
    	//@ set n.seq = \seq_concat(\seq_singleton(x), tail == null ? \seq_empty : tail.seq);
    	//@ set n.repr = \set_union(\all_fields(n), tail == null ? \empty : (\set_union(\all_fields(tail), tail.repr)));
    	return n;
    }

    
    /*@ public normal_behaviour
      @   ensures 0 <= \result;      
      @   ensures \result < seq.length && seq[\result] == 0
      @           || \result == seq.length;
      @   ensures (\forall int x; 0 <= x && x < \result; seq[x] != 0);
      @*/
    public /*@pure@*/ int search() {
	Node jj = this;
	int i = 0;
	/*@ loop_invariant 0 <= i && i <= seq.length
	  @                && (jj == null && i == seq.length
	  @                    || jj != null && jj.\inv && jj.seq == seq[i..seq.length])
	  @                && (\forall int x; 0 <= x && x < i; seq[x] != 0);
	  @ assignable \strictly_nothing;
	  @ decreases seq.length - i;
	  @*/
	while(jj != null && jj.head != 0) {
	    jj = jj.next;
	    i++;
	}
	return i;
    }
}
