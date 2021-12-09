package java.util;
import java.io.*;
// @ import java.io.*;

class T  {
    /*@ public ghost int f = 0; */

    /*@ spec_public */ void a() {
        //@ assert true;
        //@ set a = 5;
        a();
        //@ set b = 5;
        return a;
        //@ unreachable;
    }

    //@ ensures true;
    void b() {
        //@loop_invariant abc;
        while(i++!=0) i--;
    }
}