public class B {
    private int count; // Should get an error that count is not in N, even though N depends on count
    //@ public model int N;
    //@ private represents N = count;

    //@ public normal_behavior
    //@   modifies \everything;
    //@   ensures N == \old(N);  // BOGUS! This should not verify, but it does.
    public void bad() {
        count = 120;
    }
}