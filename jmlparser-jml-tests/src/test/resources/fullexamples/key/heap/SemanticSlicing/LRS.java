package unsatcore_after.competition.postcond5.scope333;

/** Implementation of the Longest Repeated Substring algorithm.
  * <em>FM 2012 Verification Competition, Problem 1 (part b).</em><br>
  * Together with a suffix array, LCP can be used to solve interesting text
  * problems, such as finding the longest repeated substring (LRS) in a text.<br>
  * A suffix array (for a given text) is an array of all suffixes of the
  * text. For the text [7,8,8,6], the suffix array is
  *   [[7,8,8,6],
  *      [8,8,6],
  *        [8,6],
  *          [6]]
  * <p>Typically, the suffixes are not stored explicitly as above but
  * represented as pointers into the original text. The suffixes in a suffix
  * array  are sorted in lexicographical order. This way, occurrences of
  * repeated substrings in the original text are neighbors in the suffix
  * array.</p>
  *
  * For the above, example (assuming pointers are 0-based integers), the
  * sorted suffix array is: [3,0,2,1]
  */
public class LRS {
    public int s = 0;
    public int t = 0;
    public int l = 0;
    public final /*@ nullable */ SuffixArray sa;

    LRS (SuffixArray arr) { sa = arr; }

    /*@
      requires (\forall int i; 0 <= i && i < sa.a.length;
                      0 <= sa.suffixes[i] && sa.suffixes[i] < sa.a.length);
      requires (\forall int i; 0 < i && i < sa.a.length; sa.suffixes[i-1] != sa.suffixes[i]);
            requires sa.a.length >= 2;

      ensures (\forall int j; 0 <= j && j < l; sa.a[s+j] == sa.a[t+j]);
      assignable s, t, l;
    @*/
    public void doLRS() {
        int s = s_0_helper();
        int t = t_0_helper();
        int l = 0;

        /*@
      maintaining (\forall int i; 0 <= i && i < sa.a.length;
                      0 <= sa.suffixes[i] && sa.suffixes[i] < sa.a.length);
               // indices are in range (follows from above, cannot hurt)
      maintaining (\forall int i; 0 < i && i < sa.a.length; sa.suffixes[i-1] != sa.suffixes[i]);
          @ maintaining 0 <= l && l < sa.a.length;
          @ maintaining 0 < x && x <= sa.a.length;
          @ maintaining (\forall int j; 0 <= j && j <l; sa.a[s+j] == sa.a[t+j]);
          @ decreasing sa.a.length-x;
          @ assignable \strictly_nothing;
          @*/
        for (int x=1; x < sa.a.length; x++) {
		int[] temp0 = sa.a;
		int temp1 = sa.suffixes[x];
		int temp2 = sa.suffixes[x-1];
		int length = LCP.lcp(temp0, temp1, temp2);
		if (b_helper()) {
			s = sa.suffixes[x];
			t = sa.suffixes[x-1];
			l = length;
		}
        }
        this.s = s;
        this.t = t;
        this.l = l;
    }

		/*@ normal_behavior
				ensures true;
				strictly_pure
		*/
		boolean b_helper(){}

		/*@ normal_behavior
				ensures true;
				strictly_pure
		*/
		int t_0_helper(){}


		/*@ normal_behavior
				ensures true;
				strictly_pure
		*/
		int s_0_helper(){}

}

//Based on code by Robert Sedgewick and Kevin Wayne.
