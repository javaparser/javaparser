class ArrayList {
    private int count;
    private /*@nullable@*/ Object[] items;
    
    
    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures size() == 0;
      @ ensures \fresh(footprint);
      @*/
    ArrayList() {
	items = new Object[10];
    }
    
    
    /*@ normal_behavior
      @ assignable footprint;
      @ ensures size() == \old(size()) + 1;
      @ ensures get(size() - 1) == o;
      @ ensures (\forall int i; 0 <= i && i < size() - 1; get(i) == \old(get(i)));
      @ ensures \new_elems_fresh(footprint);
      @ diverges true;
      @*/
    void add(/*@nullable@*/ Object o) {
	if(count == items.length) {
	    final Object[] temp = new Object[count + 10];
	    /*@ loop_invariant 0 <= i && i <= count
	      @    && (\forall int x; 0 <= x && x < i; temp[x] == items[x]);
	      @ assignable temp[*];
	      @*/
	    for(int i = 0; i < count; i++) {
		temp[i] = items[i];
	    }
	    items = temp;
	}
	items[count++] = o;
    }
    
    
    /*@ normal_behavior
      @ requires 0 <= i && i < size();
      @ assignable \nothing; 
      @ accessible footprint;
      @ ensures \result == get(i);
      @*/
    /*@nullable@*/ Object get(int i) {
	return items[i];
    }

    
    /*@ normal_behavior
      @ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == size();
      @ ensures 0 <= \result;
      @*/
    int size() {
	return count;
    }
    
    
    /*@ accessible \inv: footprint;
      @ invariant items != null;
      @ invariant 0 <= count && count <= items.length;
      @ invariant \typeof(items) == \type(Object[]);
      @*/

    
    /*@ model \locset footprint;
      @ accessible footprint: footprint;
      @ represents footprint = \storeref(count, items, items[*]);
      @*/    
}
