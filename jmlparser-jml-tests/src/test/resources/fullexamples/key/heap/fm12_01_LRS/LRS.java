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


    private int s = 0;
    private int t = 0;
    private int l = 0;
    private final SuffixArray sa;

    LRS (SuffixArray arr) { sa = arr; }


    /*@ normal_behavior
      @ requires \invariant_for(sa);
      @ requires sa.a.length >= 2;
      @ ensures 0 <= s && s < sa.a.length;
      @ ensures 0 <= t && t < sa.a.length;
      @ ensures 0 <= l && l < sa.a.length;
      @ ensures s+l <= sa.a.length && t+l <= sa.a.length;
      @ ensures (\forall int j; 0 <= j && j < l; sa.a[s+j] == sa.a[t+j]);
      @ ensures s != t || l == 0;
      @ ensures !(\exists int i,k; 0 <= i && i < k && k < sa.a.length-l;
      @            (\forall int j; 0 <= j && j <= l; sa.a[k+j] == sa.a[i+j]));
      @         // there is no LRS of length l+1
      @*/
    public void doLRS() {
        int s = 0; int t = 0; int l = 0;

        /*@ maintaining sa != null && \invariant_for(sa);
          @ maintaining 0 <= s && s < sa.a.length;
          @ maintaining 0 <= t && t < sa.a.length;
          @ maintaining 0 <= l && l < sa.a.length;
          @ maintaining s+l <= sa.a.length && t+l <= sa.a.length;
          @ maintaining s != t || l == 0;
          @ maintaining 0 < x && x <= sa.a.length;
          @ maintaining (\forall int j; 0 <= j && j <l; sa.a[s+j] == sa.a[t+j]);
          @ maintaining !(\exists int w; 0 < w && w < x
          @               && sa.suffixes[w-1] < sa.a.length-l
          @               && sa.suffixes[w]   < sa.a.length-l;
          @               (\forall int j; 0 <= j && j <= l;
          @                sa.a[sa.suffixes[w-1]+j] == sa.a[sa.suffixes[w]+j]));
          @ decreasing sa.a.length-x;
          @ assignable \strictly_nothing;
          @*/
        for (int x=1; x < sa.a.length; x++) {
            int length = LCP.lcp(sa.a,sa.suffixes[x],
                                      sa.suffixes[x-1]);
            if (length > l) {
                s = sa.suffixes[x];
                t = sa.suffixes[x-1];
                l = length;
        }   }
        this.s = s; this.t = t; this.l = l;
    }

}


//Based on code by Robert Sedgewick and Kevin Wayne.
