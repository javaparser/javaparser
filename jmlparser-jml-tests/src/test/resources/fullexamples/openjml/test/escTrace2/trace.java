public class trace {
    
    //@ requires k < 0;
    //@ ensures \result == 0;
    //@ also
    //@ requires true;
    //@ requires k >= 0;
    //@ ensures \result != 0;
    public int m(int k) {
        return 0;
    }

}