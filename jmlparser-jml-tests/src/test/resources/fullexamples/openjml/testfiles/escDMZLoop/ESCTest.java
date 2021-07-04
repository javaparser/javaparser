// This example from DMZ on 10/23 - has a problem proving the loop invariant with the exists

public class ESCTest {
  //@ requires the_array.length > 0;
  /*@ ensures (\forall int i; 0 <= i && i < the_array.length;
               the_array[i] <= \result);
   */
  /*@ ensures (\exists int i; 0 <= i && i < the_array.length;
               the_array[i] == \result);
   */
  /**
   * A method that finds the maximum value in an array.
   * 
   * @param the_array The array to find the maximum value in.
   * @return The index of the maximum value. If it appears more 
   * than once, we do not define which of the indices we return.
   */
  public /*@ pure */ int findMax(final int[] the_array) {
    int result = Integer.MIN_VALUE;
    //@ assume the_array[0] >= Integer.MIN_VALUE;
    
    //@ loop_invariant 0 <= i;
    //@ loop_invariant i <= the_array.length;
    //@ loop_invariant (\forall int j; 0 <= j && j < i; the_array[j] <= result);
    //@ loop_invariant i > 0 ==> (\exists int j; 0 <= j && j < i; the_array[j] == result);
    //@ decreasing the_array.length - i;
    for (int i = 0; i < the_array.length; i++) {
      if (result < the_array[i]) {
        result = the_array[i];
      }
    }
    
    return result;
  }
}