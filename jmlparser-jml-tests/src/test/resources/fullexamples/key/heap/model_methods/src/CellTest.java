class CellTest {

    /*@ requires \invariant_for(c); ensures c.post_set(x) && \invariant_for(c); @*/
    void callSet(Cell c, int x) {
        c.set(x);
    }

    /*@ requires \invariant_for(r); ensures r.get() == 5; @*/
    void test(Recell r) {
        r.set(5);
        callSet(r, 4);
        r.undo();
    }

    /*@ requires \invariant_for(c); ensures c.get() == 4; @*/
    void test2(Cell c) {
        c.set(5);
        callSet(c, 4);
    }

}