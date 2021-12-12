package java.util;
import java.io.*;
//@ model import java.io.*;

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

    /*@
        // example contract;
        ensures true;
        requires true;
        assignable \nothing;
    */
    void b() {
        //@loop_invariant abc;
        while(i++!=0) i--;
    }
}