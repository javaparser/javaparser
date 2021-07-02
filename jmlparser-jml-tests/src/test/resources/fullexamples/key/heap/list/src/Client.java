public class Client {
    public int x;
    
    /*@ normal_behaviour
      @   requires list.\inv && \disjoint(list.footprint, this.*);
      @   requires list.size() > 0;
      @*/
    void m(List list) {
	x++;
	Object o = list.get(0);
    }
    
    
    /*@ normal_behaviour
      @   requires list.\inv;
      @   ensures \result >= 0;
      @*/
    /*@pure@*/ int n(List list) {
	return list.size();
    }
    
    
    /*@ normal_behaviour
      @   requires list.\inv;
      @   ensures \result == (\exists int i; 0 <= i && i < list.size(); list.get(i) == this);
      @*/
    boolean /*@pure@*/ listContainsMe(List list) {
	ListIterator it = list.iterator();
	/*@ loop_invariant it.\inv && it.list == list
	  @                && 0 <= it.pos && it.pos <= list.size()
	  @                && (\forall int i; 0 <= i && i < it.pos; list.get(i) != this);
	  @ assignable it.*;
	  @ decreases list.size() - it.pos;
	  @*/
	while(it.hasNext()) {
	    if(it.next() == this) {
		return true;
	    }
	}
	return false;
    }
    
    
    //interactive proofs:
    //-listContainsMe (obvious quantifier instantiations)
}
