/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: primatives
 * 
 * @author jls
 *
 */
public class A {
    
    //@ requires true;
    public int cmp(int a, int b){
                
        if(a < b){
            return -1;
        }else{
            
            if(a > b){
                return 1;
            }
            
            return 0;
            
        }
    }
    
    
}

