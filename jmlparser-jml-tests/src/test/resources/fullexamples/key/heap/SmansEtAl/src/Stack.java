class Stack {
    private ArrayList contents;


    /*@ normal_behavior
      @ assignable \nothing;
      @ ensures size() == 0;
      @ ensures \fresh(footprint);
      @*/
    Stack() {
        contents = new ArrayList();
    }


    /*@ normal_behavior
      @ assignable footprint;
      @ ensures size() == \old(size()) + 1;
      @ ensures \new_elems_fresh(footprint);
      @ diverges true;
      @*/
    void push(/*@nullable@*/ Object o) {
        contents.add(o);
    }


    /*@ normal_behavior
      @ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == size();
      @*/
    int size() {
        return contents.size();
    }
    
    
    /*@ accessible \inv: footprint;
      @ invariant contents.\inv;
      @ invariant \disjoint(contents, contents.footprint);
      @*/
    
    
    /*@ model \locset footprint;
      @ accessible footprint: footprint;
      @ represents footprint = \set_union( \locset(contents), contents.footprint );
      @*/


    /*@ normal_behavior
      @ requires other.\inv;
      @ requires \disjoint(footprint, other.footprint);
      @ requires \typeof(other) == \type(Stack);
      @ assignable footprint, other.footprint;
      @ ensures other.\inv;
      @ //ensures size() == \old(other.size()) && other.size() == \old(size());
      @ ensures \disjoint(footprint, other.footprint);
      @ ensures \new_elems_fresh(\set_union(footprint, other.footprint));
      @*/
    void switchContents(Stack other) {
        ArrayList tmp = contents;
        contents = other.contents;
        other.contents = tmp;
    }
}
