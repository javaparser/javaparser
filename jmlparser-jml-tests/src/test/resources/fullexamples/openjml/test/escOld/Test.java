// Tests of old clauses in nested behaviors
public class Test {
    
    //@ public normal_behavior
    //@   old int iiiii = 20;
    //@   requires iiiii - 10 >= 0;
    //@   {|
    //@   requires b;
    //@   old int jjjjj = qq(iiiii);
    //@   requires a.length > 10000;
    //@   assignable a[jjjjj-100];
    //@   ensures \result == jjjjj - iiiii;
    //@   also
    //@   requires !b;
    //@   old int kkkkk = qq(10+iiiii);
    //@   ensures \result == iiiii - 20 + 100;
    //@   |}
    public int mmm(int[] a, boolean b) {
        return 100;
    }
    
    //@ public normal_behavior
    //@   requires k < 1000;
    //@   ensures \result == k + 100;
    //@ pure
    public int qq(int k) {
        return k+100;
    }
}