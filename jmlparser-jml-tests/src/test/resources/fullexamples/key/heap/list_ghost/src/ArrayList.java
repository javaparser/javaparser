final class ArrayList implements List {
    
    private /*@nullable@*/ Object[] array = new Object[10];
    private int size = 0;
    
    //@ invariant footprint == \set_union(this.*, array.*);                                      
    
    //@ invariant array != null;
    //@ invariant 0 <= size && size <= array.length;
    //@ invariant \typeof(array) == \type(Object[]);
    
    /*@ normal_behaviour
      @   ensures size() == 0;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ ArrayList() {
	//@ set footprint = \set_union(\all_fields(this), \all_fields(array)); 
    }
    
    
    /*@ normal_behavior
      @   assignable array, \singleton(footprint);
      @   ensures \fresh(array);
      @   ensures array.length > \old(array.length);
      @   ensures (\forall int x; 0 <= x && x < size; array[x] == \old(array[x]));
      @*/
    private void enlarge() {
	final Object[] newArray = new Object[array.length + 10];
	
	/*@ loop_invariant 0 <= i && i <= size 
	  @  && (\forall int x; 0 <= x && x < i; newArray[x] == array[x]);
	  @ assignable newArray[*];
	  @ decreases size - i;
	  @*/
	for(int i = 0; i < size; i++) {
	    newArray[i] = array[i];
	}
	array = newArray;
	//@ set footprint = \set_union(\all_fields(this), \all_fields(array));
    }
        

    public void add(Object o) {
	if(size == array.length) {
	    enlarge();
	}
	array[size++] = o;
    }

    
    public Object get(int index) {
	if(index < 0 || size <= index) {
	    throw new IndexOutOfBoundsException();
	}
	return array[index];
    }
    
    
    public int size() {
	return size;
    }
}
