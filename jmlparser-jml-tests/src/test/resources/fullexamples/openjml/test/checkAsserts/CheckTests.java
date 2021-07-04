public class CheckTests {
    
    public void m1(int i) {
        //@ assert i >= 0; // FAILS
        //@ assert i >= 0; // OK
    }
    
    public void m2(int i) {
        //@ assume i >= 0;
        //@ assert i >= 0; // OK
    }
    
    public void m3(int i) {
        //@ check  i >= 0; // FAILS
        //@ assert i >= 0; // FAILS
    }

}