public class LongArith2 {

    /*@ spec_public @*/ private long ub,lb;
    //@ public invariant Integer.MIN_VALUE <= lb && lb <= Integer.MAX_VALUE;
    //@ public invariant Integer.MIN_VALUE <= ub+1 && ub <= Integer.MAX_VALUE;
    
    //@ public normal_behavior
    //@   requires l <= ((long)u)+1;
    //@   assignable \nothing;
    //@   ensures lb == (long)l && ub == (long)u;
    public LongArith2(int l, int u) {
        lb = l; ub = u; 
    }

    //@ ensures \result == ub;
    public /*@ pure @*/ long upperBound() {
        return ub;
    }

    //@ ensures \result == ub - lb - 1;
    public /*@ pure @*/ long size() {
        return ub - lb - 1;
    }
}
