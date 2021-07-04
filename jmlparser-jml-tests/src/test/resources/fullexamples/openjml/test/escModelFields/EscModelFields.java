
public class EscModelFields {

    private int rep; //@ in value;
    
    //@ public model int value;
    //@ private represents value = -rep;
    
    //@ public invariant value >= 0;
    
    //@ requires v >= 0;
    //@ ensures value == v;
    //@ pure
    public EscModelFields(int v) {
        rep = -v;
    }
    
    //@ requires this != other;
    //@ modifies value; 
    //@ ensures value == (other.value + \old(value));
    public void increase(EscModelFields other) {
        //@ ghost boolean b = (\lbl SAME this == other);
        rep = rep + other.rep;
    }
    
    //@ assignable \nothing;
    //@ ensures \result.value == (other.value + value);
    public EscModelFields add(EscModelFields other) {
        int r = rep + other.rep;
        return new EscModelFields(-r);
    }
}
