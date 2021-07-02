
public class ConstructorBugTest {
	public static int count;

	/*@
	  @ ensures count == 3;
	  @*/
	public int main() {
		count = 0;
		BBug obj = new BBug();
		return count;
	}
	
//	public static void main(String[] args) {
//		BBug obj = new BBug();
//		System.out.println(count);
//	}
}

class ABug {
	
	public int a;
	
	public ABug() {
		this(42);
		ConstructorBugTest.count++;
//		System.out.println("Return A()");
	}
	
	public ABug(int a) {
		ConstructorBugTest.count++;
		this.a = a;
//		System.out.println("Return A(a)");
	}
}

class BBug extends ABug {
	public boolean b;

	public BBug() {
		ConstructorBugTest.count++;
//		System.out.println("Return B()");
	}

	public BBug(int a) {
		super(a);
		ConstructorBugTest.count++;
//		System.out.println("Return B(a)");
	}
}