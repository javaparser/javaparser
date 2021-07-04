

public class escDiverges {
    
/*@   requires 0 <= the_input;
      ensures \result == 0;
    also
      requires the_input < 0;
      diverges true;
      signals (IllegalArgumentException e) true;
      signals_only IllegalArgumentException;
*/
public double sqrt(final double the_input) 
  throws IllegalArgumentException {
  if (the_input < 0) { throw new IllegalArgumentException(); }
  return 0;
}

}

/*
I get an OpenJML ESC Error: 

"An error while executing a proof script for sort: (error "Parse Error: <shell>:1.33:Symbol Real not declared as a type")

when trying to ESC the following method (ignore the fact that it doesn't actually calculate a square root  ):

I then get an error marker saying "Not implemented for static checking: diverges clause"; which is fine, but the proof script error that popped up was pretty unnerving. Also, if I write it this way:

[ see escDiverges2 ]

It checks fine. But isn't the diverges clause in exceptional_behavior just "true" by default, the same as I had specified it in my lightweight spec? 

*/