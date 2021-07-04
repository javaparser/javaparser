/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields
 * 
 * @author jls
 *
 */
public class A7 {
    
    int THE_FIELD;
    
    //@ requires true;
    public int localTest(int a, int b){
        
        THE_FIELD = 999;

        if(THE_FIELD > -1){
            return 0;
        }
        
        THE_FIELD = 777;
        
        return -1;
    }
}

