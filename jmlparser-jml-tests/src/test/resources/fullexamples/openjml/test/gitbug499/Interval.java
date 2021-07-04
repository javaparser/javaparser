public class Interval implements IntSet {
    /*@ spec_public @*/ protected int lb, ub; //@ in state;
    /*@ spec_public @*/ protected boolean inclusive = false; //@ in state;
    //@ public invariant lb <= ub;
    //@ public invariant ub == Integer.MAX_VALUE <==> inclusive;

    //@ requires l <= u;
    //@ assignable state;
    //@ ensures lb == l && ub == u;
    public Interval(int l, int u) {
        lb = l; ub = u; 
    }

    //@ ensures \result == lb;
    public /*@ pure @*/ int lower() { return lb; }

    //@ ensures \result == ub;
    public /*@ pure @*/ int upper() { return ub; }

    //@ also
    //@   ensures \result <==> (lb <= i && i < ub) || (inclusive && i == ub);
    public /*@ pure @*/ boolean contains(int i) {
        return lb <= i && i < ub || (inclusive && i == ub);
    }

    public int choose() {
        return lb;
    }

    public void add(int i) {
        if (!contains(i)) {
            //@ assert (i < lb || i >= ub) && (!inclusive || i != ub);
            if (i < lb) {
                lb = i;
            } else {  //@ assert i >= ub && (!inclusive || i != ub);
                if (i < Integer.MAX_VALUE) {
                    ub = i+1;
                } else {
                    ub = i;
                    inclusive = true;
                }
            }
            //@ contains(i);
        }
    }

    public void remove(int i) {
        if (!contains(i)) {
            return;
        }
        //@ assert lb <= i && i < ub || (inclusive && i == ub);
        if (lb <= i && i < ub) {
            if (i-lb > ub-i) {
                lb = i+1;
            } else {
                ub = i-1;
            }
        } else if (inclusive)
            //@ assert i == ub && ub == Integer.MAX_VALUE;
            lb = i-1;
            ub = i-1;
            inclusive = false;
        }
        //@ !contains(i);
    }

    public /*@ pure @*/ int size() {
        return ub - lb - 1;
    }
}
