
/* This examples shows how the \old construct can be
 * used for method parameters.
 *
 * See bugreport #1297 for details on the problematic.
 */

class OldForParameters {
    /*@ requires i > 0;
      @ ensures \result == i;
      @*/
    int method(int i) {

        int r = 0;

        /*@ loop_invariant r + i == \old(i) && i >= 0;
          @ assignable \strictly_nothing;
          @ decreasing i;
          @*/
        while(i > 0) {
            r++;
            i--;
        }
        return r;
    }
}
