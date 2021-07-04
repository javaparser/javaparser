/**
 * 
 * Category: Non-interprocedural, loop-free
 * Features: locals, primatives, fields
 * 
 * @author jls
 *
 */
public class A9 {
    

    //@ requires true;
    public int localTest0(){
        
        int a;
        
        a = 3;
        a = 4;
        a = 5;
        
        return -1;
    }


}

