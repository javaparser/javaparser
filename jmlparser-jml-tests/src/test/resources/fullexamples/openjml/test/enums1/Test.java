enum EEE {
    
    AA, BB, CC, DD;
}

public class Test {
    
    public void m1() {
        //@ assert EEE.AA instanceof EEE;
        //@ assert \type(EEE) <: \type(Enum<EEE>);  // FIXME - needs work
        //@ assert EEE.class <: Enum.class;
    }
    
    //@ pure
    public void m2a() {
        //@ assert EEE.AA.toString().equals("AA");  // Needs work on strings
    }
    
    //@ pure
    public void m2c() {
        //@ assert EEE.AA.name().equals("AA");  // Needs work on strings
    }
    
    //@ pure
    public void m5d(EEE e) {
        //@ assume (\forall EEE ee; ee != null ==> (\exists \bigint i; 0<=i && i<EEE._JMLvalues.length; EEE._JMLvalues[i] == ee)); // FIXME - failig
        EEE[] ev = EEE.values();
        //@ assume (\forall EEE ee; ee != null ==> (\exists \bigint i; 0<=i && i<ev.length; ev[i] == ee)); // FIXME - failig
        //@ show ev, EEE._JMLvalues, ev[0], EEE._JMLvalues[0];
        //@ assert (\forall EEE ee; ee != null ==> (\exists \bigint i; 0<=i && i<ev.length; ev[i] == ee)); // FIXME - failig
    }
    
}