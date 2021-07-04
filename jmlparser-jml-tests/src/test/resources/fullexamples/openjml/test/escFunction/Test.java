// From a bug encountered in proving.
// See also the spec of Integer.asUnsignedToLong

public class Test {
	
	
	//@ public normal_behavior
	//@   ensures \result == (i<0 ? ((long)i - Integer.MIN_VALUE - Integer.MIN_VALUE) : i);
	//@   ensures 0 <= \result && \result <= 0xffff_ffffL;
	//@ pure helper function
	//@ model public static long cv(int i);
	
	//@ public normal_behavior
	//@   ensures \result == cv(i);
	//@ pure helper
	public long g(int i)  { return i & 0xffffffffL; }
	
	//@ ensures \result == cv(i);
	public long f(int i) {
		return g(i);
	}
	
	//@ public normal_behavior
	//@   ensures \result == (i<0 ? ((long)i - Integer.MIN_VALUE - Integer.MIN_VALUE) : i) && 0 <= \result && \result <= 0xffff_ffffL;
	//@ pure helper function
	//@ model public static long cv2(int i);
	
	//@ public normal_behavior
	//@   ensures \result == cv2(i);
	//@ pure helper
	public long g2(int i) { return i & 0xffffffffL; }
	
	//@ ensures \result == cv2(i);
	public long f2(int i) {
		return g2(i);
	}
	
	//@ public normal_behavior
	//@   ensures \result == (i<0 ? ((long)i - Integer.MIN_VALUE - Integer.MIN_VALUE) : i);
	//@   ensures 0 <= \result && \result <= 0xffff_ffffL;
	//@ pure helper 
	//@ model public static long cv3(int i);
	
	//@ public normal_behavior
	//@   ensures \result == cv3(i);
	//@ pure helper
	public long g3(int i)  { return i & 0xffffffffL; }
	
	//@ ensures \result == cv3(i);
	public long f3(int i) {
		return g3(i);
	}
	
	
}