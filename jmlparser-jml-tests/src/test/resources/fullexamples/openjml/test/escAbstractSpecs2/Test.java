public class Test {

	public static class C {
		
		public boolean init = true;
		
		//@ public normal_behavior
		//@   ensures init;
		//@ public C();
		
		public C(int i) {
			this();
		}
		
	}


}