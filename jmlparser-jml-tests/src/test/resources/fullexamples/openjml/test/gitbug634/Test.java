public class Test {
    private int count;  //@ in NNNN;
    private int count3;  //@ in NNNN3;
	//@ spec_public
    private int count2;  //@ in NNNN2;
    //@ public model int NNNN;
    //@ private represents NNNN = count;
    //@ public model int NNNN2;
    //@ private represents NNNN2 = count2;
    //@ public model int NNNN3;
    //@ private represents NNNN3 \such_that NNNN3 == count3;

    
    //@ public normal_behavior
    //@   assignable \everything;
    //@   ensures NNNN == \old(NNNN);  // BOGUS! This should not verify, but it does.
    public void bad() {
        count = 120;
    }
    
    //@ public normal_behavior
    //@   requires count2 == 120;
    //@   assignable \everything;
    //@   ensures NNNN2 == \old(NNNN2);
    public void good() {
        count2 = 120;
    }
    
    //@ public normal_behavior
    //@   assignable NNNN;
    //@   ensures NNNN == \old(NNNN);  // BOGUS! This should not verify, but it does.
    public void bad2() {
        count = 120;
    }
    
    //@ public normal_behavior
    //@   requires count2 == 120;
    //@   assignable NNNN2;
    //@   ensures NNNN2 == \old(NNNN2);
    public void good2() {
        count2 = 120;
    }
    
    //@ public normal_behavior
    //@   assignable NNNN3;
    //@   ensures NNNN3 == \old(NNNN3);  // BOGUS! This should not verify, but it does.
    public void bad3() {
        count3 = 120;
    }
}