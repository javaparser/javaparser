public class Test {
    
	// All loop specifications must begin with loop_
    
    //@ requires a != null && a.length > 10;
    public void mm(int[] a) {
        
        a[3] = 10;
        //@ loop_invariant 5<=i && i<=8;
        //@ assignable i,a[4..7];
        //@ writes i,a[4..7];
        for (int i= 5; i<8; i++) {
            a[i] = -4;
        }
        //@ assert a[3] == 10;  // OK
    }
    
    //@ requires a != null && a.length > 10;
    public void mok(int[] a) {
        
        a[3] = 10;
        //@ loop_invariant 5<=i && i<=8;
        //@ loop_assignable i,a[4..7];
        //@ loop_writes i,a[4..7];
        //@ loop_modifies i,a[4..7];
        for (int i= 5; i<8; i++) {
            a[i] = -4;
        }
        //@ assert a[3] == 10;  // OK
    }
    
}