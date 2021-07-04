public class Test540 implements Test540I {

    //@ also public normal_behavior
    //@   ensures \result >= i;
    @Override
    public int m(int i) {
        return i;
    }
    
    @Override
    public int md(int i) {
        return i;
    } 

}

interface Test540I {
    
    //@ public normal_behavior
    //@   ensures \result > i;
    int m(int i);
    
    //@ public normal_behavior
    //@   ensures \result > i;  // FAILS
   default int md(int i) {
        return i;
    }
}