public class Feasible {
    
    //@ requires i >= 0;
    //@ also feasible_behavior
    //@   requires i == 12;
    public int ma(int i) {
        
        if (i > 10) return i;
        //@ reachable;
        return i - 10;
    }
    
    
    //@ requires i >= 0;
    //@ also feasible_behavior
    //@   requires i == 12 || i == 2;
    public int mb(int i) {
        
        if (i > 10) return i;
        //@ reachable;
        return i - 10;
    }
    
    
    //@ requires i >= 0;
    //@ also feasible_behavior
    //@   requires i == 12 || i == -2;
    public int mc(int i) {
        
        if (i > 10) return i;
        //@ reachable;
        return i - 10;
    }
    
    
    
}