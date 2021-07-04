public class A16 {

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
    public int localTest(int a, int b){
	int tmp = add(a, b);
	
	return tmp * 100;
    }    
}
