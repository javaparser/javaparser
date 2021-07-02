class DynamicGhost {
    int x;
    C c;

    //@ public ghost \locset rep;

    //@ public invariant \subset(\locset(rep), rep);
    //@ private invariant rep == this.*;

    //@ private invariant \disjoint(rep, c.rep);
    //@ private invariant \invariant_for(c);

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_1 () {
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_2 () {
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_3 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_4 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_5 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_6 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_7 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_8 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_9 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_10 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }

    //@ normal_behavior
    //@ requires x > 0;
    //@ ensures x > 0;
    void dynamicGhost_20 () {
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
        x++; c.helper();
    }


    class C {
        int y;

        //@ public ghost \locset rep;
        //@ public invariant \subset(\locset(rep), rep);
        //@ private invariant rep == this.*;

        //@ accessible \inv: rep;

        //@ normal_behavior
        //@ ensures \new_elems_fresh(rep);
        //@ assignable rep;
        public void helper() {}
    }

}