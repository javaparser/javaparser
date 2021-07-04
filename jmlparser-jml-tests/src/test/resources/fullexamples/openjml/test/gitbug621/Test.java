public class Test {
    public AnotherClass ac = new AnotherClass();
    //@ public invariant ac.zero() == 0;

    //@ public behavior
    //@     requires true;
    public void testMethod() {
        //@ assert 0 <= ac.x;
        workerMethod();  // error
    }
    public void workerMethod() { 
    }
}
class AnotherClass {
    public int x;
    //@ public invariant 0 <= x;
    
    //@ public normal_behavior
    //@   ensures \result == 0;
    //@ pure
    public int zero() {
        return 0;
    }
}