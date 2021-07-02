public class Gcd {

    /*@
      @ public normal_behavior
      @   ensures (a != 0 || b != 0) ==>
      @           (a % \result == 0 && b % \result == 0 &&
      @            (\forall int x; x > 0 && a % x == 0 && b % x == 0;
      @                            \result % x == 0));
      @*/
    public static int gcd(int a, int b) {
        if (a < 0) a = -a;

        //@ merge_point
        //@ merge_proc "MergeByIfThenElse";

        if (b < 0) b = -b;

        //@ merge_point
        //@ merge_proc "MergeByPredicateAbstraction"
        //@ merge_params {conjunctive: (int x) -> {x >= 0, (x == \old(b) || x == -\old(b))}};

        int big, small;
        if (a > b) {
            big = a;
            small = b;
        }
        else {
            big = b;
            small = a;
        }

        return gcdHelp(big, small);
    }

    /*@
      @ public normal_behavior
      @   requires _small >= 0 && _big >= _small;
      @   ensures _big != 0 ==>
      @           (_big % \result == 0 && _small % \result == 0 &&
      @            (\forall int x; x > 0 && _big % x == 0 && _small % x == 0;
      @                            \result % x == 0));
      @ assignable \nothing;
      @*/
    private static int gcdHelp(int _big, int _small) {
        int big = _big;
        int small = _small;

    	/*@
    	  @ loop_invariant small >= 0 && big >= small &&
    	  @   (big == 0 ==> _big == 0) &&
    	  @   (\forall int x; x > 0; (_big % x == 0 && _small % x == 0)
    	  @                          <==>
    	  @                          (big % x == 0 && small % x == 0));
    	  @ decreases small;
    	  @ assignable \nothing;
    	  @*/
        while (small != 0) {
            final int t = big % small;
            big = small;
            small = t;
        }

        return big;
    }

}
