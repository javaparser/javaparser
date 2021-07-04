public class Test {
	
	public static class A {
		
		public boolean init = true;
		
		//@ public normal_behavior
		//@   ensures init;
		//@ model public A();
		
		public void m() {
			A a = new A();
			//@ assert a.init;
		}
		
	}
	
	public abstract static class B {
		
		public final String S = "";
		
		//@ also public normal_behavior
		//@   requires true;
		//@   ensures false;
		//@ non_null
		//@ abstract public String toString();
	}
	
	static public class BB extends B {
		//@ represents theString = "a";
		
		@Override
		public String toString() { return "a"; }
		
	}

}