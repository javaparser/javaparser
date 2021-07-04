public class A17 {

    public int FIELD;
    
    //@ requires true;
    //@ ensures this.FIELD==3;
    //@ ensures \result == a + b;
    //@ assignable this.FIELD;
    public int add(int a, int b){
	this.FIELD = 3;
	return a+b;
    }
    
    
    //@ requires true;
    public int localTest3(int a, int b){
	int tmp = add(a, b);
	
	if(tmp > 100){
	    return tmp * 100;
	}else{
	    return tmp * 50;	    
	}
	
    }
   

    
}
