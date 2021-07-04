
/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields in branches, fields. 
 * 
 * @author jls
 *
 */
public class A13 {
    
    int THE_FIELD;
    
    public A13 tricky;
    
    //@ requires true;
    public int localTest(int a, int b, A13 aa){
        
        THE_FIELD = 0;
        
        aa.tricky.tricky.THE_FIELD = 100;
        
        return -1;
    }
    
    
}

