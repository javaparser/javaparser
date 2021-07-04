public class B {
    //@ model public int X;
    private boolean b;  //@ in X;

    //@ private represents X = 0;
 
    //@ public behavior
    //@   assignable \everything;
    public B() {
      havocX();
      //@ assert !b;  // BAD! This does not hold after a call to havocX
    }

    //@ public normal_behavior
    //@   assignable X;
    public void havocX() {
        b = true;
    }
    
    //@ private normal_behavior
    //@ ensures b == \old(b); // This also should not be valid
    public void m() {
    	havocX();
    }
}