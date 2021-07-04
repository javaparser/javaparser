
public class FirstTest {

	int a; //@ invariant a >= 0;
	
	//@ requires a < 0;
	public void setA(int a) {
		this.a = a;
	}
	
	public String toString() {
		return ""+a;
	}
	
	public static void main(String[] args) {
	  FirstTest x = new FirstTest();
          x.setA(10);
	  System.out.println("x: "+x);
	}
}
