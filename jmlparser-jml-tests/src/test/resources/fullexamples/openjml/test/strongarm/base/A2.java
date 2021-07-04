
/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, locals in branches
 * 
 * @author jls
 *
 */
public class A2 {
    
    //@ requires true;
    public int cmp(int a, int b){
        
        int c = b++;
        
        if(a < b + c){
            return -1;
        }else{
            
            if(a > b){
                return 1;
            }
            
            return 0;
            
        }
    }
    
    
}

