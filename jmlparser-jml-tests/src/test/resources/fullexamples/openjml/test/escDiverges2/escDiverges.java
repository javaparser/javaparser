
public class escDiverges {
    

/*@ public normal_behavior
      requires 0 <= the_input;
      ensures \result == 0;
    also public exceptional_behavior
      requires the_input < 0;
      signals (IllegalArgumentException e) true;
      signals_only IllegalArgumentException;
*/
public double sqrt(final double the_input) 
  throws IllegalArgumentException {
  if (the_input < 0) { throw new IllegalArgumentException(); }
  return 0;
}

}