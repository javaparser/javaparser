public class LongArith {

    /*@ spec_public @*/ private long lb;
    /*@ spec_public @*/ private int ib;
    //@ public invariant Integer.MIN_VALUE <= lb && lb <= Integer.MAX_VALUE;
    
    public LongArith(int l) {
        lb = (long)l;
        ib = l;
    }

    //@ requires i < Integer.MAX_VALUE;
    public void use_int(int i) {
        if (!(ib <= i)) { return; }
        //@ assert ib <= i;
        ib = i+1;
        //@ assert ib == i+1;
        //@ assert ib > i;
    }

    //@ requires il < Integer.MAX_VALUE;
    public void use_long(long il) {
        if (!(lb <= il)) { return; }
        //@ assert lb <= il;
        lb = il+1;
        //@ assert lb == il+1;
        //@ assert lb > il;
    }
}
