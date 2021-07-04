public class Test {
    
    //@ public normal_behavior
    //@   requires a.length > 100;
    //@   requires i>=0 && i < 5;
    //@   old int ii = 2*i;
    //@   {|
    //@     requires j >= 0 && j < 10;
    //@   also
    //@     requires j >= 0 && j < 10;
    //@   |}
    //@   old int iij = ii + j;
    //@   assignable a[ii];
    //@   ensures \result == iij;
    public int f(int[] a, int i, int j) {
        a[i+i] = 0;
       return i + i + j;
    }
}