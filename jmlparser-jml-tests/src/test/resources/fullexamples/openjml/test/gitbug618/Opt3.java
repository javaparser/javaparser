

public class Opt3 {
	
	private Opt3(/* nullable */ Test t) {
		value = t;
	}
	
	//@ nullable 
	final public Test value;
	
	//@ public normal_behavior
	//@   { return value != null; }
	//@ pure
	public boolean nn() { return value != null; }
}
