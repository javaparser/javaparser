public class trace {
    
    static public int k;
    
    static public void mm() {}
    
    //@ requires true;
    //@ assignable k;
    //@ signals (Exception e) false;
    public void m() {
        k = 1;
        mm();
        k = 2;
        return ;
    }
    
    //@ requires true;
    //@ assignable k;
    //@ ensures k == 2;
    //@ signals (Exception e) k == 1;
    public void m2() {
        try {
            k = 1;
            mm();
            k = 2;
        } finally {}
    }
    
    //@ requires true;
    //@ assignable k;
    //@ ensures k == 2;
    //@ signals (Exception e) k == 1;
    
    public void m3() {
        try {
            k = 1;
            mm();
            k = 2;
        } catch (Exception e) {}
    }
}