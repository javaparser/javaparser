/**
 * Solution for the KeY verifier to the coincidence count challenge
 * provided by Rustan Leino at the Dagstuhl-Seminar on Verification
 * Competitions.
 *
 * The challenge was to count coincidences that is the number of
 * elements that occur in two arrays. Assumption is that both 
 * are strictly sorted.
 *
 * To provide a different modelling, we chose to use a
 * \sum-comprehension to model the count. For the coincidence count we
 * sum 1 for the elements a[i] in a for which there is an index j with
 * a[i] == b[j].
 *
 * The proof in KeY leaves 4 intermediate goals open on which the
 * sum-comprehension needs to be treated manually using
 * interaction. The proof takes c. 17000 steps on 120 branches.
 *
 * @author Mattias Ulbrich <ulbrich@kit.edu>
 */

class CC {

    /*@ public normal_behaviour
      @  requires (\forall int i,j; 0 <= i && i < j && j < a.length; 
      @                 a[i] < a[j]);
      @  requires (\forall int i,j; 0 <= i && i < j && j < b.length; 
      @                 b[i] < b[j]);
      @  ensures \result == 
      @      (\sum int k; 0<=k && k < a.length;
      @          (\exists int l; 0<=l && l<b.length; a[k]==b[l]) ? 1 : 0);
      @  modifies \strictly_nothing;
      @*/
    int calcCoinIndex(int[] a, int[] b) {
        int i = 0;
        int j = 0;
        int result = 0;

        /*@
          @ loop_invariant 
          @  0 <= i && i <= a.length && 0 <= j && j <= b.length &&
          @  (i == a.length || (\forall int l; 0 <= l && l < j; b[l] < a[i])) &&
          @  (j == b.length || (\forall int m; 0 <= m && m < i; a[m] < b[j])) &&
          @  result == 
          @   (\sum int k; 0<=k && k < i;
          @       (\exists int l; 0<=l && l<j; a[k]==b[l]) ? 1 : 0);
          @
          @ decreases a.length+b.length - i - j;
          @
          @ modifies \strictly_nothing;
          @*/
        while(i < a.length && j < b.length) {
            if(a[i] < b[j]) {
                i++;
            } else if(b[j] < a[i]) {
                j++;
            } else {
                i++; 
                j++;
                result++;
            }
        }
        return result;
    }
}
