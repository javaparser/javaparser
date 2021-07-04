public class trace {
    
    //@ requires true;
    //@ ensures \result != 0;
    public int m(int k) {
        Object o = new Object();
        //@ assert \typeof(o) == \type(Object);
        return 0;
    }
}