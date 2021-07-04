
public class RecursiveInvariant {
    
    //@ public invariant m();
    
    public /*@ pure */ boolean m() { return true; }
    
    //@ requires m();
    public void t() {}
}