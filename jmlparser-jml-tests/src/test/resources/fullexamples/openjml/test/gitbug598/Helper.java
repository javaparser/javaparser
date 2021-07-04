public class Helper {
	
	private /*@spec_public@*/ int i;
	
	/*@
	  @ public invariant i >= 0;
	  @*/
	
	/*@ 
	  @ assignable i;
	  @ signals (Exception e) false;
	  @*/
	private /*@helper@*/ void violate() {
		i = -1;
	}
	
	//warning that violate() violates the class instance invariant
	//that is to be expected since helper method are allowed to do that.
	//the warning is useless.
	/*@
	  @ assignable this.i;
	  @ requires i < Integer.MAX_VALUE;
	  @ ensures \result == i && i == \old(i) + 1;
	  @*/
	public int incrementAndGet() {
		int j = i + 1;
		violate();
		return i = j;
	}

}
