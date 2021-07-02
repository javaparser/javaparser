public interface List {
    
    //@ public ghost instance \locset footprint;
    //@ public ghost instance \seq seq;

    //@ public instance invariant \subset(\singleton(this.seq), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    //@ public instance invariant (\forall int i; 0<=i && i<seq.length; seq[i] instanceof Object);
    //@ public accessible \inv: footprint;

    /*@ public normal_behaviour
      @   accessible footprint;
      @   ensures \result == seq.length;
      @*/
    public /*@pure@*/ int size(); 
    
    
    /*@ public normal_behaviour
      @   requires 0 <= index && index < seq.length; 
      @   accessible footprint;
      @   ensures \result == seq[index];
      @
      @ also public exceptional_behaviour
      @   requires index < 0 || seq.length <= index;
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@pure@*/ Object get(int index);
    
    
    /*@ public normal_behaviour
      @   accessible footprint;
      @   ensures \result == (\exists int i; 0 <= i && i < seq.length; seq[i] == o);
      @*/
    public /*@pure@*/ boolean contains(Object o);      
    
    
    /*@ public normal_behaviour
      @   assignable footprint;
      @   ensures seq == \seq_concat(\old(seq), \seq_singleton(o));
      @   ensures \new_elems_fresh(footprint);
      @*/    
    public void add(Object o);    
    
    /* @ public normal_behaviour
      @   ensures \fresh(\result);
      @   ensures \result.list == this;
      @   ensures \result.pos == 0;
      @   ensures \result.\inv;
      @   ensures \disjoint(footprint, \result.*);
      @*/
    //   public /*@pure@*/ ListIterator iterator();
    
    
    /*@ public normal_behaviour
      @   requires (\forall int i; 0 <= i && i < seq.length; seq[i] != o);
      @   assignable \nothing;
      @
      @ also public normal_behaviour
      @   requires (\exists int i; 0 <= i && i < seq.length; seq[i] == o);
      @   assignable footprint;
      @   ensures (\exists int i; 0 <= i && i < \old(seq).length && \old(seq[i]) == o;
      @      seq == \old(\seq_concat(seq[0..i], seq[i+1..seq.length])));
      @   ensures \new_elems_fresh(footprint);
      @*/
    public void remove(Object o);
    
}
