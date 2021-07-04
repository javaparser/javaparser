public class Test {
	
	   //@ public normal_behavior
	//@      requires i != Integer.MIN_VALUE;
	   //@   ensures i == F.finverse( F.f( i ) );
	   //@ model public static pure void testInverse(int i) { }

	public static class F {
		//@ ensures \result == -i-1; pure
		public static int f(int i) { return ~i; }
		//@  ensures \result == ~i; pure
		public static int finverse(int i) { return ~i; }
	}
	
	public void m(int i) {
		
		//@ assert ~i == -i -1;
		//@ assert ~0 == -1;
		//@ assert ~1 == -2;
		//@ assert ~-1 == 0;
		//@ assert ~Integer.MIN_VALUE == Integer.MAX_VALUE;
		//@ assert Integer.MIN_VALUE == ~Integer.MAX_VALUE;
		//@ assert ~~i == i;
	}
	   
	public void m(long i) {
		
		//@ assert ~i == -i -1;
		//@ assert ~0 == -1;
		//@ assert ~1 == -2;
		//@ assert ~-1 == 0;
		//@ assert ~Long.MIN_VALUE == Long.MAX_VALUE;
		//@ assert Long.MIN_VALUE == ~Long.MAX_VALUE;
		//@ assert ~~i == i;
	}
	   
}