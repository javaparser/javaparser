interface List {
    
    //@ ghost instance \locset footprint;
    //@ accessible \inv: footprint;
    
    /*@ normal_behaviour
      @   assignable footprint;
      @   ensures size() == \old(size()) + 1;
      @   ensures get(size() - 1) == o;
      @   ensures (\forall int i; 0 <= i && i < size() - 1; get(i) == \old(get(i)));
      @   ensures \new_elems_fresh(footprint);
      @*/ 
     public void add(/*@nullable@*/ Object o);
         
    /*@ normal_behaviour
      @   requires 0 <= index && index < size(); 
      @   accessible footprint;
      @   ensures \result == get(index);
      @
      @ also exceptional_behaviour
      @   requires index < 0 || size() <= index;
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@pure nullable@*/ Object get(int index);
    
    /*@ normal_behaviour
      @   accessible footprint;
      @   ensures \result == size();
      @*/
    public /*@pure@*/ int size();
}
