
public class A15 {

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
	return add(a, b);
    }
    

    
}
