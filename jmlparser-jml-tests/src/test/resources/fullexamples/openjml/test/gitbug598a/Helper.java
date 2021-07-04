public class Helper {
	
	private /*@spec_public@*/ int i;
	
	/*@
	  @ public invariant i >= 0;
	  @*/
	
	/*@ 
	  @ assignable i;
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
		violate(); // Specs allow an exceptional exit here, in which case the invariant is not satisfied
		return i = j;
	}

}
