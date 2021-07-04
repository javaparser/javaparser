public class trace {
    
    public int f;
    static public int sf;
    public int[] a = { 1,2,3};
    
    public void mm(int k,boolean b) {};
    
    //@ ensures \result == 41;
    public int mmm(int k) { return 41;};
    
    //@ requires true;
    //@ ensures \result != 0;
    public int m(int k) {
        int j = 0;
        mm(k+k,k==0);
        mmm(9);
        j = mmm(j+1) + mmm(10) + mmm(j);
        return 0;
    }
}