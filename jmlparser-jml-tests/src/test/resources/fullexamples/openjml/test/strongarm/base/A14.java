
public class A14 {

    int THE_FIELD;
    
    //@ requires true;
    public int localTest(int a, int b){
        
        THE_FIELD = 999;

        if(a > -1){
            THE_FIELD = 867;
            
            if(a == 1){
        	THE_FIELD = 111;
        	return 1;
            }
            
            return 0;
        }
        
        THE_FIELD = 777;
        return -1;
    }
    

    
}
