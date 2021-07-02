// Stolen from examples/standard_key/arith/euclidean/src/Gcd.java
// and adapted.
public class GreatestCommonDivisor {

    // Automatically provable with options:
    //  'Block treatment': Contract;
    //  'Arithmetic treatment': DefOps.
    /*@ public normal_behavior
      @ requires a != 0 || b != 0;
      @ ensures (a % \result == 0 && b % \result == 0 &&
      @         (\forall int x; x > 0 && a % x == 0 && b % x == 0; \result % x == 0));
      @ assignable \nothing;
      @*/
    public static int ofWith(final int a, final int b)
    {
        /*@ normal_behavior
          @ ensures a >= 0 && (a == \before(a) || a == -\before(a));
          @ ensures b >= 0 && (b == \before(b) || b == -\before(b));
          @ assignable \nothing;
          @*/
        {
            if (a < 0) a = -a;
            if (b < 0) b = -b;
        }
        final int small;
        final int big;
        /*@ normal_behavior
          @ ensures a <= b ==> small == a && big == b;
          @ ensures a >  b ==> small == b && big == a;
          @ ensures small >= 0 && big >= small;
          @ assignable \nothing;
          @*/
        {
            if (a <= b) {
                small = a;
                big = b;
            }
            else {
                small = b;
                big = a;
            }
        }
        int currentBig = big;
        int currentSmall = small;
        /*@ public normal_behavior
          @ requires small >= 0 && big >= small;
          @ ensures big != 0 ==> (big % currentBig == 0 && small % currentBig == 0
          @                       && (\forall int x; x > 0 && big % x == 0 && small % x == 0; currentBig % x == 0));
          @ assignable \nothing;
          @*/
        {
            /*@ loop_invariant currentSmall >= 0 && currentBig >= currentSmall
              @                && (currentBig == 0 ==> big == 0)
              @                && (\forall int x; x > 0; (currentBig % x == 0 && currentSmall % x == 0)
              @                                           <==> (big % x == 0 && small % x == 0));
              @ decreases currentSmall;
              @ assignable \nothing;
              @*/
            while (currentSmall != 0) {
                final int remainder = currentBig % currentSmall;
                currentBig = currentSmall;
                currentSmall = remainder;
            }
        }
        return currentBig;
    }

    /*@ public normal_behavior
      @ requires a != 0 || b != 0;
      @ ensures (a % \result == 0 && b % \result == 0 &&
      @         (\forall int x; x > 0 && a % x == 0 && b % x == 0; \result % x == 0));
      @ assignable \nothing;
      @*/
    public static int ofWithout(final int a, final int b)
    {
        {
            if (a < 0) a = -a;
            if (b < 0) b = -b;
        }
        final int small;
        final int big;
        {
            if (a <= b) {
                small = a;
                big = b;
            }
            else {
                small = b;
                big = a;
            }
        }
        int currentBig = big;
        int currentSmall = small;
        {
            /*@ loop_invariant currentSmall >= 0 && currentBig >= currentSmall
              @                && (currentBig == 0 ==> big == 0)
              @                && (\forall int x; x > 0; (currentBig % x == 0 && currentSmall % x == 0)
              @                                           <==> (big % x == 0 && small % x == 0));
              @ decreases currentSmall;
              @ assignable \nothing;
              @*/
            while (currentSmall != 0) {
                final int remainder = currentBig % currentSmall;
                currentBig = currentSmall;
                currentSmall = remainder;
            }
        }
        return currentBig;
    }

}
