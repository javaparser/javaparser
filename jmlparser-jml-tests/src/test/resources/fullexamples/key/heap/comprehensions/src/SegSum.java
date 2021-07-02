/**
 * Taken from the paper
 *    "Reasoning about Comprehensions with First-Order SMT Solvers" 
 * by Rustin Leino and Rosemary Monahan
 */
public class SegSum {

    /*@ public normal_behaviour
      @ requires 0 <= i && i<=j && j<a.length;
      @ ensures result == (\sum int k; i <=k & k<j; a[k]);
      @*/
    public static int segSum(int[] a, int i, int j) {
	int s = 0; 
	/*@ loop_invariant i<=n && n<=j &&
	  @    s == (\sum int k; i <=k & k<n; a[k]);
	  @ assignable \nothing;
	  @ decreases j-n;
	  @*/
	for (int n=i; n<j; n++) {
	    s += a[n];
	}
	return s;
    }

}