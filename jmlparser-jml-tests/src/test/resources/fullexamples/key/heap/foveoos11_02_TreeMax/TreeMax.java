public final class Tree {

    int value;
    /*@ nullable @*/ Tree left;
    /*@ nullable @*/ Tree right;

    /*@ invariant left == null <==> right == null;
      @ invariant left != null ==> 
      @                   (\invariant_for(left) && \invariant_for(right));
      @*/

    /*@ ghost int height;
      @ invariant height >= 0;
      @ invariant left != null ==>
      @                   height > left.height && height > right.height;
      @*/

    /*@ ghost \set values;
      @ invariant values == \dl_cup(\dl_single(value),
      @           (left==null)? \dl_emptySet()
      @                       : \dl_cup(left.values,right.values));
      @*/

    /*@ normal_behavior
      @ ensures (\forall int z; \dl_contains(z,values); z <= \result);
      @ ensures \dl_contains(\result,values);
      @ measured_by height;
      @ strictly_pure
      @*/
    int max () {
        int res = value;
        if (left != null) {
            res = maxHelper(res,left.max(),right.max());
        }
        return res;
    }

    /*@ normal_behavior
      @ ensures \result >= x;
      @ ensures \result >= y;
      @ ensures \result >= z;
      @ ensures \result == x || \result == y || \result == z;
      @ strictly_pure helper
      @*/
    int maxHelper(int x, int y, int z) {
        if (x > y) return (x > z? x: z);
        else return (y > z? y: z);
    }
}
