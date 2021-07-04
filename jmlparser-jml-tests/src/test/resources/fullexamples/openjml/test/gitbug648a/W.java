public class W {

    public void m() {
        int x = X.qqq();  // ERROR - no visible specs
        //@ assert x == 701; // FAILS to prove because specs are not visible
    }

    //@ public normal_behavior
    //@   ensures true;
    public int mm() {
        int x = X.qqq();  // ERROR - no visible specs
        return x;
    }
}

class X {
    
    //@ private normal_behavior
    //@   ensures \result == 701;
    static public int qqq() {
        return 701;
    }
}