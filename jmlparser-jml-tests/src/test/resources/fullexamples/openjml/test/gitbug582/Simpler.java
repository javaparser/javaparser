public class Simpler {
	
	static public class H {
		
		//@ model public nullable Object content;
		
		public static boolean b; //@ in content;
		
		//@ public normal_behavior
		//@   ensures true;
		//@ pure
		public boolean has(Object o) { return b; }
		
		//@ public normal_behavior
		//@  assignable this.content;
		public void take(Object o) {}
	}
	
	
	
	//@ ensures !h.has(o);
	public void loop(H h, Object o) {
		while (h.has(o)) {
			h.take(o);
		}
		//@ assert !h.has(o);
	}
	
	//@ ensures !h.has(o);
	public void loop2(H h, Object o) {
		for (; h.has(o); ) {
			h.take(o);
		}
		//@ assert !h.has(o);
	}

	//@ ensures !h.has(o);
	public void loop3(H h, Object o) {
		do {
			h.take(o);
		} while (h.has(o));
		//@ assert !h.has(o);
	}

	//@ requires !h.has(o);
	//@ ensures !h.has(o);
	public void loop4(int[] a, H h, Object o) {
		//@ loop_invariant !h.has(o);
		for (int k: a) {
			h.take(o);
			//@ assume !h.has(o);
		} while (h.has(o));
		//@ assert !h.has(o);
	}

	//@ requires !h.has(o);
	//@ ensures !h.has(o);
	public void loop4(java.util.List<Object> a, H h, Object o) {
		//@ loop_invariant !h.has(o);
		for (Object k: a) {
			h.take(o);
			//@ assume !h.has(o);
		}
		//@ assert !h.has(o);
	}

}