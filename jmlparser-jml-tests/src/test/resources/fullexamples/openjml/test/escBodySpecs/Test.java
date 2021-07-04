public class Test {
    
    //@ requires i < 100;
    //@ ensures \result == i;
    public int m(int i) {
        
        int a = i + 1;
        //@ refining normal_behavior
        //@   assignable a;
        //@   ensures a == i+10;
        {
            a += 9;
        }
        return a - 10;
    }
    
    
}