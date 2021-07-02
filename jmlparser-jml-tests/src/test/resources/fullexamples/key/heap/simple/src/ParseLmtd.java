/*
 * This class is for testing the parsing of "$lmtd".
 * If "$lmtd" is not parsed correctly, the proof can be saved, but not reloaded.
 * Corresponding bug is #1447.
 */

class ParseLmtd {

    ParseLmtd next;
    int f;
    int c;
    
    //@ model int mf;
    //@ represents mf = next.mf*c + f ;
    
    /*@ normal_behavior
      @   requires (\forall int x; x*c == 0);
      @   ensures mf > \old(mf);
      @*/
    void simple(int n) {
        f ++;
    }
}
