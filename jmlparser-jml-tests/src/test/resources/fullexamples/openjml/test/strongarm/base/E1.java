public class E1 {
    
    //@ requires true;
    public static int m0(int a, int b){
	
	if(a < 0 || b < 0 || a + b < 10 || a - b < 10 || a * b < 10){
	    return a - b;
	}

	return a + b;	
    }
}
