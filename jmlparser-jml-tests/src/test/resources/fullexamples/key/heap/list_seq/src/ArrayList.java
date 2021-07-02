public class ArrayList implements List {
    
    private /*@nullable@*/ Object[] array;
    private int size = 0;
    
    /*@ private invariant array != null;
      @ private invariant footprint == \set_union(array[*], this.*);
      @ private invariant 0 <= size && size <= array.length;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] != null);
      @ private invariant \typeof(array) == \type(Object[]);
      @ private invariant seq.length == size;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] == seq[i]);
      @*/
    
    
    /*@ public normal_behaviour
      @   ensures seq == \seq_empty && \fresh(footprint);
      @*/
    public /*@pure@*/ ArrayList() {
	this.array = newArray(10);
	//@set seq = \seq_empty;
	//@set footprint = \set_union(\all_fields(array), \all_fields(this));
	{}
    }

    /*@ private normal_behavior
      @   requires l >= 0;
      @   ensures \typeof(\result) == \type(Object[]);
      @   ensures \result.length == l;
      @   ensures \fresh(\result);
      @   ensures \result != null;
      @   assignable \nothing;
      @*/
    private /*@helper*/ /*@nullable*/Object[] newArray(int l) {
	return new Object[l];
    }
    
    
    /*@ private normal_behavior
      @   assignable \singleton(footprint), \singleton(array);
      @   ensures \fresh(array);
      @   ensures \old(array.length) < array.length;
      @   ensures (\forall int x; 0 <= x && x < size; array[x] == \old(array[x]));
      @*/
    private void enlarge() {
	final Object[] newArray = newArray(array.length + 10);
	//@ set footprint = \set_union(\set_union(\all_fields(newArray), \all_fields(this)), \all_fields(this));
	
	/*@ loop_invariant 0 <= i && i <= size 
	  @  && (\forall int x; 0 <= x && x < i; newArray[x] == array[x]);
	  @ assignable newArray[*];
	  @ decreases size - i;
	  @*/
	for(int i = 0; i < size; i++) {
	    newArray[i] = array[i];
	}
	array = newArray;
    }

    
    public int size() {
	return size;
    }
    
    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	return array[index];
    }   
    
    
    public boolean contains(Object o) {
	/*@ loop_invariant 0 <= i && i <= size
	  @  && (\forall int x; 0 <= x && x < i; array[x] != o);
	  @ assignable \nothing;
	  @ decreases size - i;
	  @*/
	for(int i = 0; i < size; i++) {
	    if(array[i] == o) {
		return true;
	    }
	}
	return false;
    }  
        

    public void add(Object o) {
	if(size == array.length) {
	    enlarge();
	}
	array[size++] = o;
	//@set seq = \seq_concat(seq, \seq_singleton(o));
	{}
    }
       
    public void remove(Object o) {
	/*@ loop_invariant 0 <= i && i <= size
	  @  && (\forall int x; 0 <= x && x < i; array[x] != o);
	  @ assignable \nothing;
	  @ decreases size - i;
	  @*/
	for(int i = 0; i < size; i++) {
	    if(array[i] == o) {
		/*@ loop_invariant i <= j && j < size
		  @  && (\forall int x; 0 <= x && x < i; array[x] == \old(array[x]))
		  @  && (\forall int x; i <= x && x < j; array[x] == \old(array[x+1]))
		  @  && (\forall int x; j <= x && x < size; array[x] == \old(array[x]));
		  @ assignable array[*];
		  @ decreases size - 1 - j;
		  @*/
		for(int j = i; j < size - 1; j++) {
		    array[j] = array[j+1];
		}
		size--;
		//@ set seq = \seq_concat(\seq_sub(seq, 0, i), \seq_sub(seq,i+1, \seq_length(seq)));
		return;
	    }
	}
    }
}
