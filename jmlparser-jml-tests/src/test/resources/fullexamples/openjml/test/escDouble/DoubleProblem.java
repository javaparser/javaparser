//-@ immutable
public /*@ pure @*/ strictfp class DoubleProblem {

    /** The double that is the abstract value of this object.
     */
    //@ model public double theDouble;

    //@ public invariant !Double.isNaN(theDouble);
	//@ axiom Double.isFinite(0.0d);

    /*@ spec_public @*/ private double doubleValue;
    //@                                   in theDouble;
    //@ public represents theDouble = doubleValue;

    /** Initialize this object to be zero. */
    /*@   public normal_behavior
      @     ensures theDouble == 0.0d;
      @*/
    public DoubleProblem() {
        doubleValue = 0.0d;
    }

    /** Initialize this object to contain the value of the given
     * Double.
     */
    /*@   public normal_behavior
      @     requires inDouble != null && !inDouble.isNaN();
      @     ensures Double.identical(doubleValue,inDouble.doubleValue());
      @*/
    public DoubleProblem(/*@ non_null */ Double inDouble) {
        doubleValue = inDouble.doubleValue();
    }

    /** Return the double contained in this object.
     */
    /*@ public normal_behavior
      @   ensures Double.identical(\result,doubleValue);
      @   ensures_redundantly !Double.isNaN(\result);
      @*/
    public double doubleValue() {
        return doubleValue;
    }

    /** Tell if this object contains NaN (not a number).
     */
    /*@ public normal_behavior
      @   ensures \result <==> Double.isNaN(theDouble);
      @*/
    public boolean isNaN() {
	return Double.isNaN(doubleValue);
    }
}
