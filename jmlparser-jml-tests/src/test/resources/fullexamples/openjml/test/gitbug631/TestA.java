//@ non_null_by_default
public class TestA {
    
    public int value;
    public int other;
    
    //@ public normal_behavior
    //@   ensures value == v && other == o;
    //@ pure
    public TestA(int v, int o) {
        value = v;
        other = o;
    }
    
    //@ public normal_behavior
    //@   assignable value;
    //@   ensures value == v;
    public void set(int v) {
        value = v;
    }
    
    public void m(TestA t) {
        //@ assume t.value == 1;
        //@ assume t.other == 2;
        t.value = 3;
        
        //@ assert t.other == 2;
        //@ assert t.value == 3;
    }
    
    public void ms(TestA t) {
        //@ assume t.value == 1;
        //@ assume t.other == 2;
        t.set(3);
        
        //@ assert t.other == 2;
        //@ assert t.value == 3; 
    }
    
    //@ requires t.length > 10;
    //@ requires t[0] != null;
    public void ma(TestA[] t) {
        //@ assume t[0].value == 1;
        //@ assume t[0].other == 2;
        t[0].value = 3;
        
        //@ assert t[0].other == 2;
        //@ assert t[0].value == 3;
    }
    
    //@ requires t.length > 10;
    //@ requires t[0] != null;
    public void msa(TestA[] t) {
        //@ assume t[0].value == 1;
        //@ assume t[0].other == 2;
        t[0].set(3);
        
        //@ assert t[0].other == 2;
        //@ assert t[0].value == 3;
    }
    

    //@ requires t.length > 10;
    //@ requires t[0] != null;
    //@ requires t[0].length > 10;
    //@ requires t[0][0] != null;
    public void maa(TestA[][] t) {
        //@ assume t[0][0].value == 1;
        //@ assume t[0][0].other == 2;
        t[0][0].value = 3;
        
        //@ assert t[0][0].other == 2;
        //@ assert t[0][0].value == 3;
    }
    
    //@ requires t.length > 10;
    //@ requires t[0] != null;
    //@ requires t[0].length > 10;
    //@ requires t[0][0] != null;
    public void msaa(TestA[][] t) {
        //@ assume t[0][0].value == 1;
        //@ assume t[0][0].other == 2;
        t[0][0].set(3);
        
        //@ assert t[0][0].other == 2;
        //@ assert t[0][0].value == 3;
    }
    
    public void mt(TestA t) {
        //@ assume t.value == 1;
        //@ assume this.value == 1;
        t.set(3);
        
        //@ assert this.value == 1; // ERROR - should fail
        //@ assert t.value == 3; 
    }

    //@ requires t != this;
    public void mt2(TestA t) {
        //@ assume t.value == 1;
        //@ assume this.value == 1;
        t.set(3);
        
        //@ assert this.value == 1;
        //@ assert t.value == 3; 
    }

    //@ requires t.length > 10;
    //@ requires t[0] != null;
    //@ requires t[1] != null;
    public void max(TestA[] t) {
        //@ assume t[0].value == 1;
        //@ assume t[1].value == 1;
        t[0].set(3);
        
        //@ assert t[1].value == 1;  // Fails
        //@ assert t[0].value == 3;
    }

    //@ requires t.length > 10;
    //@ requires t[0] != null;
    //@ requires t[1] != null;
    public void max1(TestA[] t) {
        //@ assume t[0].value == 1;
        //@ assume t[1].value == 1;
        //@ assume t[0] != t[1];
        t[0].set(3);
        
        //@ assert t[1].value == 1;
        //@ assert t[0].value == 3;
    }

    //@ requires t.length > 10;
    //@ requires t[0] != null;
    //@ requires t[1] != null;
    public void max2(TestA[] t) {
        //@ assume t[0].value == 1;
        //@ assume t[1].value == 2;
        t[0].set(3);
        
        //@ assert t[1].value == 2;
        //@ assert t[0].value == 3;
    }

}