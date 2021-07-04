
public class RecursiveInvariantMQ {
    
    //@ public invariant m();

    public /*@ pure */ boolean m() { return true; }
    
    //@ requires m();
    public void t() {}
}