public class Test {
    
    //@ requires a != null && a.length > 10;
    public void m(int[] a) {
        
        a[3] = 10;
        //@ loop_invariant 5<=i && i<=8;
        for (int i= 5; i<8; i++) {
            a[i] = -4;
        }
        //@ assert a[3] == 10; // Not proved since the default loop_modifies is a[*]
    }
    
    //@ requires a != null && a.length > 10;
    public void mm(int[] a) {
        
        a[3] = 10;
        //@ loop_invariant 5<=i && i<=8;
        //@ loop_modifies i,a[4..7];
        for (int i= 5; i<8; i++) {
            a[i] = -4;
        }
        //@ assert a[3] == 10;  // OK
    }
}