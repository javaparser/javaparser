/**
 * 
 * Category: interprocedural, loop-free
 * Features: primatives
 * 
 * @author jls
 *
 */
public class B {
    
    /*@ 
      public normal_behavior
      requires true; 
      {| 
         ensures a==b ==> \result == true;
        also
         ensures a!=b ==> \result == false;
       |}
     */
    public boolean areEqual(int a, int b){
        return a-b == 0;
    }
    
    //@ requires true;
    public int cmp(int a, int b){
        

        if(areEqual(a,b)){
            return 0;
        }
        
        if(a < b){
            return -1;
        }
        
        return 1;
    }
    
    
}

