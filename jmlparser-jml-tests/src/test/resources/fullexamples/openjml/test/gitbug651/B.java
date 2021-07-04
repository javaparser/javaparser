public class B {
    private int count;  //@ in N;
    //@ public model int N;
    //@ private represents N = count;

    //@ public normal_behavior
    //@   modifies \everything;
    //@   ensures N == \old(N);  // BOGUS! This should not verify, but it does.
    public void bad() {
        count = 120;
    }
}