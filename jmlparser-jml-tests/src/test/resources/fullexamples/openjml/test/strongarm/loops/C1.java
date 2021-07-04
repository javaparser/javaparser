
public class C1 {

    
    //@ requires ar!=null;
    public static int sum(int ar[]){
	int sum = 0;
	/*@ 
          @ maintaining -1 < i && i <= ar.length;
          @ maintaining sum == i;
          @ decreasing ar.length - i;
          @*/
	for(int i=0; i < ar.length; i++){
	    sum += 1;
	    int tmp = sum;
	    
	    for(int j=0; j < ar.length; j++){ // an extra loop, just to be tricky
		sum++;
	    }
	    
	    sum=tmp;
	}
	
	//sum = 36;
	
	return sum;
    }
}
