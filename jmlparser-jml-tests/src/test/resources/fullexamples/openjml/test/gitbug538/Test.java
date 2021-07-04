public class Test {
    
    public int n;
    
    //@ public invariant n > 0;
    
    //@ public behavior
    //@    ensures n == nn;
    //@ pure
    public Test(int nn) {
        if (nn <= 0) throw new RuntimeException();
        this.n = nn;
    }
}