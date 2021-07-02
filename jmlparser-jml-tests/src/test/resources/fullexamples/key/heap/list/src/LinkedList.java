final class LinkedList implements List {
        
    private /*@nullable@*/ Node first;
    private /*@nullable@*/ Node last;
    private int size;
    
    //@ private represents footprint = first, last, size, \reachLocs(first.next, first);
    
    /*@ private invariant size == 0 && first == null && last == null
      @                   || size > 0
      @                      && first != null 
      @                      && last != null 
      @                      && last.next == null
      @                      && \reach(first.next, first, last, size - 1);
      @ private invariant (\forall int i; 0 <= i && i < size; (\forall Node n; \reach(first.next, first, n, i); n.data != null));
      @*/
   
    
    /*@ normal_behaviour
      @   ensures size() == 0;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ LinkedList() {
    }
    
    
    public int size() {
	return size;
    }
    
    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	
	Node node = first;
	/*@ loop_invariant 0 <= i && i <= index && \reach(first.next, first, node, i);
	  @ assignable \nothing;
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
	/*@ loop_invariant 0 <= i && i < size && \reach(first.next, first, node, i)
	  @   && (\forall int x; 0 <= x && x < i; get(x) != o);
	  @ assignable \nothing;
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
    

    public void add(Object o) {
	Node node = new Node();
	node.data = o;
	if(size == 0) {
	    first = node;
	    last = node;
	} else {
	    last.next = node;
	    last = node;
	}
	size++;
    }
    
    
    public ListIterator iterator() {
	return null;//TODO
    }
    
    
    public void remove(Object o) {
	//TODO
    }
    
    
    public void concatenate(List l) {
	//TODO
    }    
}
