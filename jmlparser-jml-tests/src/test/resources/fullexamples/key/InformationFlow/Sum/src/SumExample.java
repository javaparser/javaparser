/**
 * Information flow example.
 *
 * The example demonstrates precise declassification: the sum of the entries
 * of an array are declassified, nothing else.
 *
 * @author Christoph Scheben
 */
class SumExample {

    private int[] values;


    public SumExample(int[] values) {
        this.values = values;
    }


    /*@ normal_behavior
      @     determines  \result \by \nothing
      @                 \declassifies  (\bsum int i; 0; values.length; values[i]);
      @*/
    public int getSum() {
        int sum = 0;
        /*@ loop_invariant
          @     0 <= i
          @  && i <= values.length
          @  && sum == (\bsum int j; 0; i; values[j]);
          @ assignable \strictly_nothing;
          @ decreases values.length - i;
          @*/
        for (int i = 0; i < values.length; i++) {
            sum += values[i];
        }
        return sum;
    }
}