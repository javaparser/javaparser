
public class RecursiveInvariant2 {
    
    //@ public invariant m();
    
    //@ ensures \result;
    public /*@ pure */ boolean m() { return true; }
    
    //@ requires m();
    public void t() {}
}