public class Test {
    
    //@ public normal_behavior
    //@   requires java.math.BigInteger.parseable(s, 10);
    //@   old \bigint b = java.math.BigInteger.parse(s,10);
    public int m(String s) {
        return 0;
    }
    
    //@ public normal_behavior
    //@   old \bigint b = 10;
    //@   ensures \result == b;
    public int mb() {
        return 10;
    }
    
    //@ public normal_behavior
    //@   old \real b = 10;
    //@   ensures \result == b;
    public double mr(String s) {
        return 10;
    }
    
    // FIXME - not yet implemented
//    //@ public normal_behavior
//    //@   old \TYPE b = \type(void);
//    public void mm(Integer t) {
//        
//    }

}