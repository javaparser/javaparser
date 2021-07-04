public class Test {
	
	//@ requires i > 0;;
	//@ ensures true;
	public void m(int i) {
		//@ assert i > 0;
	}
	
	//@ requires true;
	public int k;
	
	//@ requires true;
	//@ model public int kk;

	//@ requires true;
	public static class C{}
	
	//@ requires true;
	//@ model public static class CC{}
	
	;
	
	//@ requires true;
	;
	
	//@ requires true;
	//@ invariant true;
	
	//@ requires true;
	//@ constraint true;
	
	//@ requires true;
	//@ axiom true;
	
	//@ requires true;
	//@ initially true;

}