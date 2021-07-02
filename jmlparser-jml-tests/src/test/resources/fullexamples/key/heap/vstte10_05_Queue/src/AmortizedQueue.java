public class AmortizedQueue {
    
    //The front of the queue.
    private final LinkedList front;

    //The rear of the queue (stored in reversed order).
    private final LinkedList rear;
       
    //@ public final ghost \seq seq;
    //@ public final ghost \locset repr;

    
    /*@ private invariant front.\inv && rear.\inv;
      @ private invariant \disjoint(this.*, \set_union(front.repr, rear.repr));      
      @ private invariant rear.seq.length <= front.seq.length;
      @ private invariant seq == \seq_concat(front.seq, \seq_reverse(rear.seq));
      @ private invariant repr == \set_union(this.*, \set_union(front.repr, rear.repr));
      @*/
    
    //@ public accessible \inv: repr;
    
    
    /**
     * Constructs an empty queue.
     */
    /*@ public normal_behaviour 
      @   ensures seq == \seq_empty;
      @   ensures \fresh(repr);
      @*/
    public /*@pure@*/ AmortizedQueue() {
	front = new LinkedList();
	rear = new LinkedList();
	//@ set seq = \seq_empty;
	//@ set repr = \set_union(\all_fields(this), \set_union(front.repr, rear.repr));
    }
    
    
    /**
     * Constructs a new queue whose front is 'front' and whose rear
     * is 'rear'.
     * 
     * 'front' and 'rear' should be non-null.
     */
    /*@ public normal_behaviour
      @   requires f.\inv && r.\inv;
      @   ensures seq == \seq_concat(f.seq, \seq_reverse(r.seq));
      @   ensures \fresh(\set_minus(repr, \set_union(f.repr, r.repr)));
      @*/
    public /*@pure@*/ AmortizedQueue(LinkedList f, LinkedList r) {
	if(r.length() <= f.length()) {
	    front = f;
	    rear = r; 
	} else {
	    LinkedList rev = r.reverse();
	    front = f.concat(rev);
	    rear = new LinkedList();
	}
	//@ set seq = \seq_concat(front.seq, \seq_reverse(rear.seq));
	//@ set repr = \set_union(\all_fields(this), \set_union(front.repr, rear.repr));
    }
    
    
    /**
     * Returns the first element of a non-empty queue.
     */
    /*@ public normal_behaviour
      @   requires seq.length != 0;
      @   ensures \result == seq[0];
      @*/
    public /*@pure@*/ int front() {
	return front.head();
    }
    
    
    /**
     * Returns a new queue that contains all elements of
     * this queue (non-empty) except for the first element.
     */
    /*@ public normal_behaviour
      @   requires seq.length != 0;
      @   ensures \result.\inv;
      @   ensures \result.seq == seq[1..seq.length];
      @   ensures \fresh(\set_minus(\result.repr, repr));
      @*/
    public /*@pure@*/ AmortizedQueue tail() {
	LinkedList t = front.tail();
	return new AmortizedQueue(t, rear);
    }
    
    
    /**
     * Returns a new queue that contains all elements of this queue
     * and an additional element "item" at the rear of the queue.
     */
    /*@ public normal_behaviour
      @   ensures \result.\inv;
      @   ensures \result.seq == \seq_concat(seq, \seq_singleton(item));
      @   ensures \fresh(\set_minus(\result.repr, repr));
      @*/
    public /*@pure@*/ AmortizedQueue enqueue(int item) {
	LinkedList r = rear.cons(item);
	return new AmortizedQueue(front, r);
    }
}
