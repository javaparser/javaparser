enum EEE {
    
    AA(4), BB(8), CC(7);
    
    //@ spec_public
    private int code;
    
    //@ public final static invariant AA.code == 4;
    //@ public final static invariant BB.code == 8;
    //@ public final static invariant CC.code == 7;
    
    //@ private normal_behavior
    //@   ensures code == c;
    //@ pure
    private EEE(int c) { code = c; }
}

public class Test {
    
    public void m0() {
        //@ show EEE.AA.code, EEE.BB.code;
        //@ assert EEE.AA.code == 4;
        //@ assert EEE.BB.code == 8;
        //@ assert EEE.CC.code == 7;
    }
    
    public void m1() {
        //@ assert EEE.AA.code == 9; // Expected failure
    }
    
}