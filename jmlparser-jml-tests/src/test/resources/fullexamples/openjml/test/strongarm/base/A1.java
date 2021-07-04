
/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives
 * 
 * @author jls
 *
 */
public class A1 {
    
    //@ requires true;
    public int cmp(int a, int b){
        
        int c = a;
        
        if(c < b){
            return -1;
        }else{
            
            if(c > b){
                return 1;
            }
            
            return 0;
            
        }
    }
    
    
}

