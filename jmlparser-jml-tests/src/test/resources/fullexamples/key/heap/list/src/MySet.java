public class MySet {
    
    //@ public model \locset footprint;
    //@ public accessible \inv: footprint;    
    //@ public accessible footprint: footprint;
    
    private List list;
       
    //@ private represents footprint = this.*, list.footprint;

    
    /*@ private invariant list.\inv;
      @ private invariant \disjoint(list.footprint, this.*);
      @ private invariant (\forall int x, y; 0 <= x && x < list.size() && 0 <= y
      @                                             && y < list.size() && x != y; 
      @                                      list.get(x) != list.get(y));
      @*/
    
    
    /*@ public normal_behaviour
      @   ensures (\forall Object x; !contains(x));
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ MySet() {
	this.list = new ArrayList();
    }   
        
    
    /*@ public normal_behaviour
      @   requires initial.\inv;
      @   requires \disjoint(initial.footprint, this.*);
      @   requires (\forall int x, y; 0 <= x && x < initial.size() && 0 <= y 
      @                                && y < initial.size() && x != y; 
      @                               initial.get(x) != initial.get(y));
      @   ensures (\forall Object x; 
      @              contains(x) ==  (\exists int y; 0 <= y && y < initial.size(); initial.get(y) == x));
      @   ensures \subset(footprint, \set_union(this.*, initial.footprint));
      @*/
    public /*@pure@*/ MySet(List initial) {
	this.list = initial;
    }
    
    
    /*@ normal_behaviour
      @   accessible footprint;
      @   ensures \result == contains(o);
      @*/
    public /*@pure@*/ boolean contains(Object o) {
	return list.contains(o);
    }
      

    /*@ public normal_behaviour
      @   assignable footprint;
      @   ensures (\forall Object x; contains(x) == (\old(contains(x)) || o == x));
      @   ensures \new_elems_fresh(footprint);      
      @*/
    public void add(Object o) {
	if(!list.contains(o)) {
	    list.add(o);
	}
    }
    
    
    /*@ normal_behaviour
      @   requires l.\inv;
      @   requires \disjoint(l.footprint, footprint);      
      @   assignable footprint;
      @   ensures (\forall Object x; contains(x) == (\old(contains(x)) || l.contains(x)));
      @   ensures \new_elems_fresh(footprint);
      @*/
    public void addAll(List l) {
	final ListIterator it = l.iterator();
	/*@ loop_invariant 0 <= it.pos && it.pos <= l.size()
	  @   && (\forall int x; 0 <= x && x < \old(list.size()); list.get(x) == \old(list.get(x)));
          @ assignable l.footprint;
          @ decreases l.size() - it.pos;
	  @*/
	while(it.hasNext()) {
	    add(it.next());
	}
    }

    
    /*@ normal_behaviour
      @   assignable footprint;
      @   ensures !contains(o);
      @   ensures \new_elems_fresh(footprint);
      @*/
    public void remove(Object o) {
	list.remove(o);
    }
    
    
    //interactive proofs:
    //-the second constructor (obvious quantifier instantiations)
    //-add (relatively obvious quantifier instantiations [self.list.size()])
    //-contains (obvious quantifier instantiation)
    //-remove (manual case split before applying method contract)
    //-\inv (obvious quantifier instantiations)
    
    //not yet verified:
    //-addAll
}
