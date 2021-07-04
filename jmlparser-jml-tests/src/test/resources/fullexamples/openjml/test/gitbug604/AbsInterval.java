public abstract class AbsInterval implements IntSet {
    /*@ spec_public @*/ protected long lb, ub; //@ in state;
    //@ public invariant Integer.MIN_VALUE <= lb && lb <= Integer.MAX_VALUE;
    //@ public invariant lb <= ub+1;
    //@ public invariant Integer.MIN_VALUE <= ub+1 && ub <= Integer.MAX_VALUE;

    //@ requires l <= ((long)u)+1;
    //@ assignable state;
    //@ ensures lb == (long)l && ub == (long)u;
    public AbsInterval(int l, int u) {
        lb = l; ub = u; 
    }

    //@ also
    //@   ensures \result <==> (lb <= i && i <= ub);
    public /*@ pure @*/ boolean contains(int i) {
        return lb <= i && i <= ub;
    }

    public void add(int i) {
        if (!contains(i)) {
            //@ assert (i < lb || i > ub);
            if (i < lb) {
                //@ assume i <= ub;
                lb = i;
                //@ assert contains(i);
                //@ assert lb < \old(lb) && ub == \old(ub);
            } else {  //@ assert i > ub && lb <= i;
                ub = i;
                //@ assert contains(i);
                //@ assert ub > \old(ub) && \not_assigned(lb);
            }
        }
    }

    public void remove(int i) {
        if (!contains(i)) { return; }
        //@ assert lb <= i && i <= ub;
        if (i-lb > ub-i) {
            lb = ((long)i)+1;
        } else {
            ub = ((long)i)-1;
        }
        //@ assert !contains(i);
    }

    /*@ also
      @   ensures \result == ub - lb - 1;
      @*/   
    public /*@ pure @*/ long size() {
        return ub - lb - 1;
    }
}
