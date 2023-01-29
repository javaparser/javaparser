class Iterator {
    private ArrayList list;
    private int index;


    /*@ normal_behavior
      @ requires l.\inv && l.size() >= 0;
      @ assignable \nothing;
      @ ensures list() == l;
      @ ensures \fresh(footprint);
      @ ensures_redundantly l.footprint == \old(l.footprint);   // The validity of this ensures clause follows already from
      @                                                         // the validity of the assignable clause. The reason for its
      @                                                         // introduction was (curiously) proof automatisation: the
      @                                                         // clause introduces the term "ArrayList::$footprint(heap, l)"
      @                                                         // to the sequent which is needed for the UseDependencyContract
      @                                                         // rule to match. In this particular example older KeY-versions
      @                                                         // introduced the term by accident by the right combination
      @                                                         // of applications of other rules.
      @*/
    Iterator(ArrayList l) {
        list = l;
    }


    /*@ normal_behavior
      @ requires hasNext();
      @ assignable footprint;
      @ ensures list() == \old(list());
      @ ensures \new_elems_fresh(footprint);
      @*/
    /*@nullable@*/ Object next() {
        return list.get(index++);
    }


    /*@ normal_behavior
      @ assignable \nothing;
      @ accessible footprint, list().footprint;
      @ ensures \result == hasNext();
      @*/
    boolean hasNext() {
        return index < list.size();
    }


    /*@ normal_behavior
      @ assignable \nothing;
      @ accessible footprint;
      @ ensures \result == list();
      @*/
    ArrayList list() {
        return list;
    }
    
    
    /*@ accessible \inv: footprint, list().footprint;
      @ invariant list.\inv;
      @ invariant 0 <= index && index <= list.size(); 
      @ invariant \disjoint(this.*, list.footprint);
      @*/
    
    
    /*@ model \locset footprint;
      @ accessible footprint: footprint;
      @ represents footprint = \locset(list, index);
      @*/
}
