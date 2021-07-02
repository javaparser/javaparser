public class ArrayList implements List {
    
    private /*@nullable@*/ Object[] array = new Object[10];
    private int size = 0;
    
    //@ private represents footprint = array, array[*], size;
    
    /*@ private invariant array != null;
      @ private invariant 0 <= size && size <= array.length;
      @ private invariant (\forall int i; 0 <= i && i < size; array[i] != null);
      @ private invariant \typeof(array) == \type(Object[]);
      @*/
    
    
    /*@ public normal_behaviour
      @   ensures size() == 0 && \fresh(footprint);
      @*/
    public /*@pure@*/ ArrayList() {
    }
    
    
    /*@ private normal_behavior
      @   assignable array;
      @   ensures \fresh(array);
      @   ensures \old(array.length) < array.length;
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
    }
    
    
    public ListIterator iterator() {
	return new ArrayListIterator(this);
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
		return;
	    }
	}
    }
    
    
    //@ private invariant \subset(\set_union(array, array[*]), footprint); //for concatenate
    
    public void concatenate(List l) {
	if(size == 0 && l instanceof ArrayList) {
	    array = ((ArrayList)l).array;
	    size = ((ArrayList)l).size;
	} else {
	    final Object[] newArray = new Object[size + l.size()];

	    /*@ loop_invariant 0 <= i && i <= size
	      @   && (\forall int x; 0 <= x && x < i; newArray[x] != null);
	      @ assignable newArray[*];
	      @ decreases size - i;
	      @*/
	    for(int i = 0; i < size; i++) {
		newArray[i] = array[i];
	    }
	    
	    /*@ loop_invariant size <= j && j <= newArray.length
	      @   && (\forall int x; 0 <= x && x < j; newArray[x] != null);
	      @ assignable newArray[*];
	      @ decreases newArray.length - j;
	      @*/
	    for(int j = size; j < newArray.length; j++) {
		newArray[j] = l.get(j - size);
	    }
	    
	    array = newArray;
	    size = newArray.length;
	}
    }
    
        
    private static class ArrayListIterator implements ListIterator {
	private final ArrayList arrayList; //workaround; should be ArrayList.this
	private int arrayPos = 0;
	
	//@ private represents list = arrayList;
	//@ private represents pos = arrayPos;
	
	/*@ private invariant arrayList.\inv;
	  @ private invariant 0 <= arrayPos && arrayPos <= arrayList.size;
	  @ private invariant \typeof(arrayList) == ArrayList;
	  @*/
	
	/*@ public normal_behaviour
	  @   requires l.\inv && \typeof(l) == ArrayList;
	  @   ensures list == l;
	  @   ensures pos == 0; 
	  @*/
	public /*@pure@*/ ArrayListIterator(ArrayList l) {
	    arrayList = l;
	}
	
	
	public boolean hasNext() {
	    return arrayPos < arrayList.size;
	}
    
	
	public Object next() {
	    if(arrayPos == arrayList.size) {
		throw new IndexOutOfBoundsException();
	    }
	    arrayPos++;
	    return arrayList.array[arrayPos - 1];
	}
    }
}
