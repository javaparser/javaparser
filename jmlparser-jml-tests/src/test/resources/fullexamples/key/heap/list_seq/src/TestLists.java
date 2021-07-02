public class TestLists {

    /*@ public normal_behaviour 
      @   requires t.\inv && l.\inv && \disjoint(t.footprint, l.footprint);
      @   assignable t.footprint;
      @   ensures \new_elems_fresh(t.footprint);
      @   ensures t.seq == \seq_concat(\old(t.seq), l.seq);
      @   ensures t.\inv;
      @*/
    public static void append(List t, List l) {
	append(t, l, l.size());
    }

    /*@ public normal_behaviour 
      @   requires s >= 0 && s <= l.seq.length;
      @   requires t.\inv && l.\inv && \disjoint(t.footprint, l.footprint);
      @   assignable t.footprint;
      @   ensures \new_elems_fresh(t.footprint);
      @   ensures t.seq == \seq_concat(\old(t.seq), \seq_sub(l.seq, 0, s-1));
      @   ensures t.\inv;
      @*/
    public static void append(List t, List l, int s) {
	int i = 0;

	// disjointness is redundant in the following:
	/*@ loop_invariant
	  @   0<=i && i<=s &&
	  @   t.seq == \seq_concat(\old(t.seq), \seq_sub(l.seq, 0, i-1)) &&
	  @   \new_elems_fresh(t.footprint) && \disjoint(t.footprint, l.footprint) &&
	  @   \invariant_for(t) && 
	  @   \invariant_for(l);
	  @ assignable t.footprint;
	  @ decreases s - i;
	  @*/
	while(i < s) {
	    t.add(l.get(i));
	    i++;
	}
    }
}
