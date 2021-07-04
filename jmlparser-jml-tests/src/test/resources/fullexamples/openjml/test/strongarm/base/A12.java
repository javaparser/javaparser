
/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields in branches, fields. 
 * 
 * @author jls
 *
 */
public class A12 {
    
    int THE_FIELD;
    
    //@ requires a > 100;
    public int localTest(int a, int b, A12 aa){
        
        aa.THE_FIELD = 0;
        
        if(THE_FIELD > -1){
            return 0;
        }
        
        THE_FIELD = 100;
        return -1;
    }
    
    
}

