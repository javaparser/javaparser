
public class E {
    
    public int a;
    
    
    //@ requires true;
    public int exceptional() throws Exception {
	if(this.a > 0){
	    throw new Exception("E");
	}
	
	return this.a;
    }

}
