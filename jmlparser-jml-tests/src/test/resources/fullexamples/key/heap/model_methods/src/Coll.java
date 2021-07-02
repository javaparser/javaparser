interface Coll {

    /*@ model_behavior
      @ ensures x>0 ==> \result;
      @ model boolean add_pre(int x);
      @*/

    //@ requires add_pre(x);
    void add(int x);
}

class Indirect {
    /*@ requires \invariant_for(c) && c.add_pre(v); @*/
    void callAdd(Coll c, int v) {
        c.add(v);
    }

    //@ requires \invariant_for(c1) && \invariant_for(c2);
    //@ ensures true;
    void test(Coll1 c1, Coll2 c2) {
        callAdd(c1, 42);
        callAdd(c2, -42);
    }
}

class Coll1 implements Coll {

    /*@ model boolean add_pre(int x) { return (x > 0); } @*/

    public void add(int x) { }

}


final class Coll2 implements Coll { 

    /*@ model boolean add_pre(int x) { return true; } @*/

    public void add(int x) { }

}