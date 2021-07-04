
//@ non_null_by_default immutable
public class Opt2 {
	
	private Opt2(/* nullable */ Object t) {
		value = t;
	}
	
	//@ nullable 
	final public Object value;
	
	//@ public normal_behavior
	//@   ensures \result == (value != null);
	//@ pure function
	public boolean nn() { return value != null; }
}