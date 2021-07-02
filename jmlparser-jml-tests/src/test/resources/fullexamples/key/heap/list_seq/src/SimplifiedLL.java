final class SimplifiedLinkedList {
        
    private /*@nullable@*/ Node first;
    private int size;

    /*@ private ghost \seq nodeseq; */
    
    /*@
      @ private invariant (\forall int i; 0<=i && i<size; 
      @         ((Node)nodeseq[i]) != null  // this implies \typeof(nodeseq[i]) == \type(Node)
      @      && (\forall int j; 0<=j && j<size; (Node)nodeseq[i] == (Node)nodeseq[j] ==> i == j)
      @      && ((Node)nodeseq[i]).next == (i==size-1 ? null : (Node)nodeseq[i+1]));
      @
      @ private invariant size > 0;
      @ private invariant first == (Node)nodeseq[0];
      @ private invariant size == nodeseq.length;
      @*/
    

    /*@ normal_behaviour
      @ requires n >= 0 && n < size && \invariant_for(this);
      @ ensures \result == (Node)nodeseq[n];
      @ assignable \strictly_nothing;
      @ helper */
    private Node getNext(int n) {
	Node result = first;
	/*@ loop_invariant
	  @   0<=i && i <=n && result == (Node)nodeseq[i];
	  @ decreases n-i;
	  @ assignable \strictly_nothing;
	  @*/
	for(int i = 0; i < n; i++) {
	    result = result.next;
	}
	return result;
    }

    /*@ normal_behaviour
      @ requires i > 0 && i < size;
      @ ensures nodeseq == \old(\seq_concat(nodeseq[0..i], nodeseq[i+1..nodeseq.length]));
      @*/
    public void remove(int i) {
	Node node = getNext(i-1);
	Node node2 = getNext(i);
	node.next = node2.next;
        //@ set nodeseq = (\seq_concat(\seq_sub(nodeseq,0,i), \seq_sub(nodeseq,i+1,\seq_length(nodeseq))));
	size --;
    }
}
