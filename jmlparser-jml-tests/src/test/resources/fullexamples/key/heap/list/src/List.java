public interface List {
    
    //@ public model instance \locset footprint;
    //@ public accessible \inv: footprint;
    //@ public accessible footprint: footprint;  
    
    //@ public instance invariant 0 <= size();
    
    
    /*@ public normal_behaviour
      @   accessible footprint;
      @   ensures \result == size();
      @*/
    public /*@pure@*/ int size(); 
    
    
    /*@ public normal_behaviour
      @   requires 0 <= index && index < size(); 
      @   accessible footprint;
      @   ensures \result == get(index);
      @
      @ also public exceptional_behaviour
      @   requires index < 0 || size() <= index;
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@pure@*/ Object get(int index);
    
    
    /*@ public normal_behaviour
      @   accessible footprint;
      @   ensures \result == (\exists int i; 0 <= i && i < size(); get(i) == o);
      @*/
    public /*@pure@*/ boolean contains(Object o);      
    
    
    /*@ public normal_behaviour
      @   assignable footprint;
      @   ensures size() == \old(size()) + 1 && get(size() - 1) == o;
      @   ensures (\forall int i; 0 <= i && i < size() - 1; get(i) == \old(get(i)));
      @   ensures \new_elems_fresh(footprint);
      @*/    
     public void add(Object o);
    
    
    /*@ public normal_behaviour
      @   ensures \fresh(\result);
      @   ensures \result.list == this;
      @   ensures \result.pos == 0;
      @   ensures \result.\inv;
      @   ensures \disjoint(footprint, \result.*);
      @*/
    public /*@pure@*/ ListIterator iterator();
    
    
    /*@ public normal_behaviour
      @   requires (\forall int i; 0 <= i && i < size(); get(i) != o);
      @   assignable \nothing;
      @
      @ also public normal_behaviour
      @   requires (\exists int i; 0 <= i && i < size(); get(i) == o);
      @   assignable footprint;
      @   ensures size() == \old(size()) - 1;
      @   ensures (\exists int i; 0 <= i && i < \old(size()) && \old(get(i)) == o;
      @              (\forall int j; 0 <= j && j < i; get(j) == \old(get(j)))
      @              && (\forall int k; i <= k && k < size(); get(k) == \old(get(k+1))));
      @   ensures \new_elems_fresh(footprint);
      @*/
    public void remove(Object o);
    
    
    /*@ public normal_behaviour 
      @   requires l.\inv && \disjoint(footprint, l.footprint);
      @   assignable footprint;
      @   ensures \new_elems_fresh(\set_minus(footprint, l.footprint));
      @*/
    public void concatenate(List l);
}
