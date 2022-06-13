package java.util;

import java.io.*;
//@ model import java.io.*;

class T {
    /*@ public ghost int f1 = 0; */

    /*+key@ public ghost int f2 = 0; */
    /*+key@ public ghost int f3 = 0; */

    /*+openjml@ public ghost int f3 = 0; */

    /*+openjml@ invariant x == 1; */


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
        while (i++ != 0) i--;
    }
}