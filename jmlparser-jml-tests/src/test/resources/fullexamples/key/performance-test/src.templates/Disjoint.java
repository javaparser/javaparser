/**
 *
 * @author christoph
 */
public class Disjoint {
    int x, y;
    //@ ghost \locset rep;
    //@ ghost \locset rep1;
    //@ ghost \locset rep2;
    //@ ghost \locset rep3;
    //@ ghost \locset rep4;
    //@ ghost \locset rep5;
    //@ ghost \locset rep6;
    //@ ghost \locset rep7;
    //@ ghost \locset rep8;
    //@ ghost \locset rep9;
    //@ ghost \locset rep10;
    //@ ghost \locset rep11;
    //@ ghost \locset rep12;
    //@ ghost \locset rep13;
    //@ ghost \locset rep14;
    //@ ghost \locset rep15;
    //@ ghost \locset rep16;
    //@ ghost \locset rep17;
    //@ ghost \locset rep18;
    //@ ghost \locset rep19;
    //@ ghost \locset rep20;


    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_1() {
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_2() {
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_3() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_4() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_5() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_6() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_7() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_8() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_9() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_10() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
     */
    void xZero_20() {
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
        xZeroHelper();
    }

    /*@ requires    x == 0;
        ensures     x == 0;
        assignable  y;
     */
    void xZeroHelper(){
    }



    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_1() {
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_2() {
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_3() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_4() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_5() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_6() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_7() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_8() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_9() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_10() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
     */
    void disjoint_20() {
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
        disjointHelper();
    }

    /*@ requires    \disjoint(\locset(x), rep);
        ensures     \disjoint(\locset(x), rep);
        assignable  y, rep;
     */
    void disjointHelper() {
    }


    /*@ requires    \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep1);
     */
    void disjoint2_1() {
        disjointHelper2_1();
    }


    /*@ requires    \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep1);
        assignable  rep1;
     */
    void disjointHelper2_1() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
     */
    void disjoint2_2() {
        disjointHelper2_2();
    }


    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        assignable  rep1, rep2;
     */
    void disjointHelper2_2() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
     */
    void disjoint2_3() {
        disjointHelper2_3();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        assignable  rep1, rep2, rep3;
     */
    void disjointHelper2_3() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
     */
    void disjoint2_4() {
        disjointHelper2_4();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        assignable  rep1, rep2, rep3, rep4;
     */
    void disjointHelper2_4() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
     */
    void disjoint2_5() {
        disjointHelper2_5();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        assignable  rep1, rep2, rep3, rep4, rep5;
     */
    void disjointHelper2_5() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
     */
    void disjoint2_6() {
        disjointHelper2_6();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6;
     */
    void disjointHelper2_6() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
     */
    void disjoint2_7() {
        disjointHelper2_7();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7;
     */
    void disjointHelper2_7() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
     */
    void disjoint2_8() {
        disjointHelper2_8();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8;
     */
    void disjointHelper2_8() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
     */
    void disjoint2_9() {
        disjointHelper2_9();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9;
     */
    void disjointHelper2_9() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
     */
    void disjoint2_10() {
        disjointHelper2_10();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9, rep10;
     */
    void disjointHelper2_10() {
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        requires    \disjoint(rep, rep11);
        requires    \disjoint(rep, rep12);
        requires    \disjoint(rep, rep13);
        requires    \disjoint(rep, rep14);
        requires    \disjoint(rep, rep15);
        requires    \disjoint(rep, rep16);
        requires    \disjoint(rep, rep17);
        requires    \disjoint(rep, rep18);
        requires    \disjoint(rep, rep19);
        requires    \disjoint(rep, rep20);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep11);
        ensures     \disjoint(rep, rep12);
        ensures     \disjoint(rep, rep13);
        ensures     \disjoint(rep, rep14);
        ensures     \disjoint(rep, rep15);
        ensures     \disjoint(rep, rep16);
        ensures     \disjoint(rep, rep17);
        ensures     \disjoint(rep, rep18);
        ensures     \disjoint(rep, rep19);
        ensures     \disjoint(rep, rep20);
     */
    void disjoint2_20() {
        disjointHelper2_20();
    }

    /*@ requires    \disjoint(rep, rep1);
        requires    \disjoint(rep, rep2);
        requires    \disjoint(rep, rep3);
        requires    \disjoint(rep, rep4);
        requires    \disjoint(rep, rep5);
        requires    \disjoint(rep, rep6);
        requires    \disjoint(rep, rep7);
        requires    \disjoint(rep, rep8);
        requires    \disjoint(rep, rep9);
        requires    \disjoint(rep, rep10);
        requires    \disjoint(rep, rep11);
        requires    \disjoint(rep, rep12);
        requires    \disjoint(rep, rep13);
        requires    \disjoint(rep, rep14);
        requires    \disjoint(rep, rep15);
        requires    \disjoint(rep, rep16);
        requires    \disjoint(rep, rep17);
        requires    \disjoint(rep, rep18);
        requires    \disjoint(rep, rep19);
        requires    \disjoint(rep, rep20);
        ensures     \disjoint(rep, rep1);
        ensures     \disjoint(rep, rep2);
        ensures     \disjoint(rep, rep3);
        ensures     \disjoint(rep, rep4);
        ensures     \disjoint(rep, rep5);
        ensures     \disjoint(rep, rep6);
        ensures     \disjoint(rep, rep7);
        ensures     \disjoint(rep, rep8);
        ensures     \disjoint(rep, rep9);
        ensures     \disjoint(rep, rep10);
        ensures     \disjoint(rep, rep11);
        ensures     \disjoint(rep, rep12);
        ensures     \disjoint(rep, rep13);
        ensures     \disjoint(rep, rep14);
        ensures     \disjoint(rep, rep15);
        ensures     \disjoint(rep, rep16);
        ensures     \disjoint(rep, rep17);
        ensures     \disjoint(rep, rep18);
        ensures     \disjoint(rep, rep19);
        ensures     \disjoint(rep, rep20);
        assignable  rep1, rep2, rep3, rep4, rep5, rep6, rep7, rep8, rep9, rep10,
                    rep11, rep12, rep13, rep14, rep15, rep16, rep17, rep18,
                    rep19, rep20;
     */
    void disjointHelper2_20() {
    }
}
