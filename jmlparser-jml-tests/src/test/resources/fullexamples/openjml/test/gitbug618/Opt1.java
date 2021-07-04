

//@ non_null_by_default immutable
public final class Opt1 {
	
	private Opt1(/* nullable */ Object t) {
		value = t;
	}
	
	//@ nullable spec_public
	final private Object value;
	
	//@ public normal_behavior
	//@   { return value != null; }
	//@ pure function
	public boolean nn() { return value != null; }
}
