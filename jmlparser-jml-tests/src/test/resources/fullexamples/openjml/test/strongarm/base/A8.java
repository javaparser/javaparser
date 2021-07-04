/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields
 * 
 * @author jls
 *
 */
public class A8 {
    
    int THE_FIELD;
    
    //@ requires true;
    public int localTest(int a, int b){
        
        THE_FIELD = 999;

        if(a > -1){
            return 0;
        }else{
            if(a > -2){
                THE_FIELD = 888;
                return 100;
            }
        }
        
        THE_FIELD = 777;
        return -1;
    }
    
    
}

