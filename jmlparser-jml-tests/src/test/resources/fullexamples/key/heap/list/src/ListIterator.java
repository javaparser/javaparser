interface ListIterator {
    
    //@ public model instance List list;
    //@ public model instance int pos;
    
    //@ accessible list: this.*;
    //@ accessible pos: this.*;
    //@ accessible \inv: this.*, list.footprint;
    
    
    /*@ normal_behaviour
      @   accessible this.*, list.footprint;
      @   ensures \result == pos < list.size();
      @*/
    public /*@pure@*/ boolean hasNext();
    
    
    /*@ normal_behaviour
      @   requires pos < list.size();
      @   assignable this.*;
      @   ensures \result == list.get(\old(pos));
      @   ensures list == \old(list);
      @   ensures pos == \old(pos) + 1;
      @ also exceptional_behaviour
      @   requires pos >= list.size();
      @   assignable \nothing;
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@nullable@*/ Object next();
}
