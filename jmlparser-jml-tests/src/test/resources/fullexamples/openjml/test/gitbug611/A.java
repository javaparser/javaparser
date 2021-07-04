interface AA {
	
	// BUG - explicit this gets the type of the parent and so A.test does not see the spoecs from A.ok
	// when reasoning about this.ok in A.test.
	// The implicit this in test2 works OK.
	
	//@ ensures \result == this.ok(i);
	public boolean test(int i);
	
	//@ ensures \result == ok(i);
	public boolean test2(int i);
	
	//@ pure
	public boolean ok(int i);
}

public class A implements AA {
	public int lb;
	
	//@ also ensures \result == (i>=lb);
	public boolean ok(int i) { return i>=lb; }
	
	public boolean test(int i) {
		return ok(i);
	}
	
	public boolean test2(int i) {
		return ok(i);
	}
	
}