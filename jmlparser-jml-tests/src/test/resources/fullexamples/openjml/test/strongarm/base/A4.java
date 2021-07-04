/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, locals in branches, fields. 
 * 
 * @author jls
 *
 */
public class A4 {
    
    int THE_FIELD;
    
    //@ requires true;
    public int localTest(int a, int b){
        
        int c = a;

        THE_FIELD = 100;

        if(c > -1){
            return 0;
        }
        
        THE_FIELD = 100;
        return -1;
    }
    
    
}

