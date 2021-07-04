
/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields
 * 
 * @author jls
 *
 */
public class A10 {
    
    
    //@ requires true;
    public int localTest1(){
        
        int a=0;
       
        
        if(a > -1){
            a = 3;
            a = 4;
        }
        
        a = 5;
        
        return -1;
    }


}

