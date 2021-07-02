final class LinkedList implements List {
        
    private /*@nullable@*/ Node first;
    private /*@nullable@*/ Node last;
    private int size;

    /*@ private ghost \seq nodeseq; */
    
    /*@
      @ private invariant footprint == \set_union(this.*,
      @      (\infinite_union int i; 0<=i && i<size; ((Node)nodeseq[i]).*));
      @
      @ private invariant (\forall int i; 0<=i && i<size; 
      @         ((Node)nodeseq[i]) != null  // this implies \typeof(nodeseq[i]) == \type(Node)
      @      && ((Node)nodeseq[i]).data == seq[i] 
      @      && (\forall int j; 0<=j && j<size; (Node)nodeseq[i] == (Node)nodeseq[j] ==> i == j)
      @      && ((Node)nodeseq[i]).next == (i==size-1 ? null : (Node)nodeseq[i+1]));
      @
      @ private invariant first == (size == 0 ? null : (Node)nodeseq[0]);
      @ private invariant last == (size == 0 ? null : (Node)nodeseq[size-1]);
      @
      @ private invariant size == seq.length && size == nodeseq.length;
      @*/
    
    /*@ normal_behaviour
      @   ensures seq == \seq_empty;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ LinkedList() {
	//@ set footprint = \all_fields(this);
	//@ set seq = \seq_empty;
	first = null;
    }
        
    public int size() {
	return size;
    }
    
    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i <= index && node == (Node)nodeseq[i];
	  @ assignable \strictly_nothing;
	  @ decreases index - i;
	  @*/
	for(int i = 0; i < index; i++) {
	    node = node.next;
	}
	
	return node.data;
    }    
    
    
    public boolean contains(Object o) {
	if(size == 0) {
	    return false;
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i < size && node == (Node)nodeseq[i]
	  @   && (\forall int x; 0 <= x && x < i; seq[x] != o);
	  @ assignable \strictly_nothing;
	  @ decreases size - 1 - i;
	  @*/
	for(int i = 0; i < size - 1; i++) {
	    if(node.data == o) {
		return true;
	    }
	    node = node.next;
	}
	
	return node.data == o;
    }    
    

    /*@ private normal_behaviour
      @   ensures \fresh(\result);
      @   ensures \result.data == o;
      @   ensures \result.next == null;
      @   assignable \nothing;
      @*/
    private Node newNode(Object o) {
	Node result = new Node();
	result.data = o;
	return result;
    }

    public void add(Object o) {
	Node node = newNode(o);
	if(size == 0) {
	    first = node;
	    last = node;
	} else {
	    last.next = node;
	    last = last.next;
	}
	//@ set seq = \seq_concat(seq, \seq_singleton(o));
	//@ set nodeseq = \seq_concat(nodeseq, \seq_singleton(node));
	//@ set footprint = \set_union(footprint, \all_fields(node));
	size++;
    }
    
    // proved!
    public void remove(Object o) {
	if(size == 0)
	    return;

	if(first.data == o) {
	    //@ set footprint = \set_minus(footprint, \all_fields(first));
	    first = first.next;
	    if(first == null) {
		last = null;
	    }
	    //@ set seq = \seq_sub(seq, 1, \seq_length(seq)-1);
	    //@ set nodeseq = \seq_sub(nodeseq, 1, \seq_length(nodeseq)-1);
	    size--;
	    return;
	}

	Node n = first.next;
	Node m = first;
	/*@ loop_invariant 1 <= i && i <= seq.length && (n == null || n == (Node)nodeseq[i])
	  @    && m == (Node)nodeseq[i-1] && (n==null ==> i == seq.length)
          @    && (\forall int j; 0<=j && j<i; seq[j] != o);
	  @ assignable \strictly_nothing;
	  @ decreases seq.length - i;
	  @*/
	for(int i = 1; n != null; i++) {
	    if(n.data == o) {
		m.next = n.next;
		if(n == last) {
		    last = m;
		}
		//@ set seq = \seq_concat(\seq_sub(seq,0,i-1), \seq_sub(seq,i+1,\seq_length(seq)-1));
		//@ set nodeseq = \seq_concat(\seq_sub(nodeseq,0,i-1), \seq_sub(nodeseq,i+1,\seq_length(nodeseq)-1));
		//@ set footprint = \set_minus(footprint, \all_fields(n));
		size --;
		return;
	    }
            m = m.next;
            n = n.next;
	}

    }
}
