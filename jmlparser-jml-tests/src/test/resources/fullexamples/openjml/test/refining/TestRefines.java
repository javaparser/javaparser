public class TestRefines {
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 11;
    public int m1(int i) {
        
        int j = 0;
        //@ refining
        //@ assignable j;
        //@ ensures j >= 11; // OK
        //@ begin
        j = i + 10;
        j++;
        //@ end
        return j;
    }
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 12;
    public int m2(int i) {
        
        int j = 0;
        //@ refining
        //@ assignable j;
        //@ ensures j >= 11;  // ERROR
        {
        j = i + 10;
        j++;
        }
        return j;
    }
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 11;
    public int m3(int i) {
        
        //@ refining : j;
        //@ assignable j;
        //@ ensures j >= 11; // OK
        //@ begin
        int j = 0;
        j = i + 10;
        j++;
        //@ end
        return j;
    }
    
    int f;
    
    //@ requires 0 <= i <= 100;
    //@ ensures \result >= 11;
    public int m4(int i) {
        
        //@ refining : j;
        //@ assignable j;
        //@ ensures j >= 11;
        //@ begin
        int j = 0;
        j = i + 10;
        j++;
        //@ end
        return j;
    }
    
    //@ public normal_behavior
    //@   ensures \fresh(\result);
    public Object m5(int i) {
        
        //@ refining : o;
        //@  ensures \fresh(o);
        //@ begin
        Object o = q();
        //@ end
        
        //@ assert o != null;
        return o;
    }
    
    //@ public normal_behavior
    //@   ensures \fresh(\result);
    //@ pure 
    static public Object q() { return new Object(); }
    
    
    
    
    
}