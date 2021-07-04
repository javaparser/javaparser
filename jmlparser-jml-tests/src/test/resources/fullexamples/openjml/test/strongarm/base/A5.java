/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields in branches, fields. 
 * 
 * @author jls
 *
 */
public class A5 {
    
    int THE_FIELD;
    
    //@ requires true;
    public int localTest(int a, int b){
        
        if(THE_FIELD > -1){
            return 0;
        }
        
        THE_FIELD = 100;
        return -1;
    }
    
    
}

