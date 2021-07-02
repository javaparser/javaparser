package unsatcore_after.competition.postcond5.scope333;

/** Contains an implementation for the Longest Common Prefix algorithm.
  * <em>FM 2012 Verification Competition, Problem 1 (part a).</em><br>
  * Longest Common Prefix (LCP) is an algorithm used for text querying. In
  * the following, we model text as an integer array. <ul>
  * <li> Input:  an integer array a, and two indices x and y into this array
  * <li> Output: length of the longest common prefix of the subarrays of a
  *     starting at x and y respectively.</ul>
  * @author bruns, woj
  */
final class LCP {

/*@ normal_behavior
  @ requires 0 <= x && x < a.length;
  @ requires 0 <= y && y < a.length;
  @ requires x != y;
  @ ensures 0 <= \result;
  @ ensures \result <= a.length - x;
  @ ensures \result <= a.length - y;
  @ ensures (\forall int i; 0 <= i && i < \result;
  @                         a[x+i] == a[y+i] );
  @ strictly_pure @*/

public static int lcp(/*@ nullable */ int[] a, int x, int y) {
    int l = 0;
    /*@ maintaining 0 <= l && l+x <= a.length
      @             && l+y <= a.length && x!=y;
      @ maintaining (\forall int z; 0 <= z && z < l;
      @                          a[x+z] == a[y+z] );
      @ decreasing a.length-l;
      @ assignable \strictly_nothing; @*/
    while (x+l<a.length && y+l<a.length && a[x+l]==a[y+l]){
	int yy = yy_0_helper(); // int yy = 0;
	yy = yy_1_helper(); // yy++;
	l++;
    }
    return l;
}


				/*@ normal_behavior
				ensures true;
				strictly_pure
		*/
		static int yy_0_helper(){}

				/*@ normal_behavior
				ensures true;
				strictly_pure
		*/
		static int yy_1_helper(){}

}
