public class D {

    // this demonstrates propagation that differs between join paths
    
    //@ requires true;
    public static int pathing(int a){
	int c = a;
	
	if(c < 10){
	    c = 100;
	}
	
	return c;
    }
}
