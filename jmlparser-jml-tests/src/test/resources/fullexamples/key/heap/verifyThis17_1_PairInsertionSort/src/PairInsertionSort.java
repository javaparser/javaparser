/**
 * This Pair Insertion Sort in which two elements are handled at a time
 * is used by Oracle's implementation of the Java Development Kit (JDK)
 * for sorting primitive values, where a is the array to be sorted, and
 * the integer variables left and right are valid indices into a that
 * set the range to be sorted.
 * This was the first challenge from the VerifyThis competition @ ETAPS 2017
 * organized by M. Huisman, R. Monahan, P. Müller, W. Mostowski,
 * and M. Ulbrich.
 * The specification considers only sortedness, the permutation property
 * is yet to be done.
 * @author Michael Kirsten <kirsten@kit.edu>
 */
public class PairInsertionSort {

    /*@ public normal_behaviour
      @ requires 0 < left && left <= right && right < a.length;
      @ //requires right - left + 1 < 47;
      @ requires (\forall int i; left - 1 <= i && i <= right; a[left - 1] <= a[i]);
      @ assignable a[left..right];
      @ ensures (\forall int i; \old(left) - 1 <= i && i < \old(right); a[i] <= a[i + 1]);
      @*/
    public static void /*@ helper @*/ sort(int[] a, int left, int right) {

	/*@ loop_invariant right == \old(right) && \old(left) <= \old(right);
	  @ loop_invariant right == \old(right);
	  @ loop_invariant k == left;
	  @ loop_invariant \old(left) <= k && k <= \old(right) + (\old(right) - \old(left)) % 2;
	  @ loop_invariant (left - \old(left)) % 2 == 0;
	  @ loop_invariant (\old(right) + 2 - left) % 2 == (\old(right) - \old(left)) % 2;
	  @ loop_invariant (\forall int i; \old(left) - 1 <= i && i <= \old(right); a[\old(left) - 1] <= a[i]);
	  @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < left - 1; a[i] <= a[i + 1]);
	  @ assignable a[left..(right - 1 + (right - left) % 2)], left, k;
	  @ decreases \old(right) + 1 - left;
	  @*/
	for (int k = left; ++left <= right; k = ++left) {
	    int a1 = a[k];
	    int a2 = a[left];

	    /*@ public normal_behaviour
	      @ requires a1 == a[k] && a2 == a[left] && left <= \old(right);
	      @ assignable \strictly_nothing;
	      @ ensures a1 == ((a[k] <= a[left]) ? a[left] : a[k]);
	      @ ensures a2 == ((a[k] < a[left]) ? a[k] : a[left]);
	      @ ensures a2 <= a1;
	      @*/
            {
                if (a1 < a2) {
                    a2 = a1;
                    a1 = a[left];
                }
            }

	    /*@ loop_invariant right == \old(right) && \old(left) <= \old(right) && \old(left) < left && k < left;
	      @ loop_invariant right == \old(right);
	      @ loop_invariant \old(left) <= k && left <= \old(right) - 1 + (\old(right) - \old(left)) % 2 && k <= \old(right) - 2 + (\old(right) - \old(left)) % 2;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i <= \old(right); a[\old(left) - 1] <= a[i]);
	      @ loop_invariant a[\old(left) - 1] <= a1;
	      @ loop_invariant a2 <= a1;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < k - 1; a[i] <= a[i + 1]);
	      @ loop_invariant \old(left) <= k && k < left - 1 ==> a[k - 1] <= a[k + 2];
	      @ loop_invariant \old(left) - 1 <= k && k < left - 1 ==> a[k] <= a[k + 2];
	      @ loop_invariant (\forall int i; k + 2 <= i && i < left; a[i] <= a[i + 1]);
	      @ loop_invariant (\forall int i; k <= i && i < left - 1; a1 < a[i]);
	      @ loop_invariant (\forall int i; k + 2 <= i && i <= left; a1 < a[i]);
	      @ assignable a[(\old(left))+2..left], k;
	      @ decreases k;
	      @*/
	    while (a1 < a[--k]) {
		a[k + 2] = a[k];
	    }

	    a[++k + 1] = a1;

	    /*@ loop_invariant right == \old(right) && \old(left) <= \old(right) && \old(left) < left && k < left;
	      @ loop_invariant right == \old(right);
	      @ loop_invariant \old(left) <= k && left <= \old(right) - 1 + (\old(right) - \old(left)) % 2 && k <= \old(right) - 2 + (\old(right) - \old(left)) % 2;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i <= \old(right); a[\old(left) - 1] <= a[i]);
	      @ loop_invariant a[\old(left) - 1] <= a2;
	      @ loop_invariant a2 <= a1;
	      @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < k - 1; a[i] <= a[i + 1]);
	      @ loop_invariant \old(left) <= k && k < left ==> a[k - 1] <= a[k + 1];
	      @ loop_invariant (\forall int i; k + 1 <= i && i < left; a[i] <= a[i + 1]);
	      @ loop_invariant (\forall int i; k <= i && i < left - 1; a2 <= a[i]);
	      @ loop_invariant (\forall int i; k + 1 <= i && i <= left; a2 <= a[i]);
	      @ loop_invariant (\forall int i; k + 2 <= i && i <= left; a2 < a[i]);
	      @ assignable a[(\old(left)+1)..left-1], k;
	      @ decreases k;
	      @*/
	    while (a2 < a[--k]) {
		a[k + 1] = a[k];
	    }

	    a[k + 1] = a2;
	}

	int last = a[right];

	/*@ loop_invariant left == \old(right) + 1 + (\old(right) - \old(left)) % 2;
	  @ loop_invariant \old(left) <= right && right <= \old(right);
	  @ loop_invariant (\forall int i; \old(left) - 1 <= i && i <= \old(right); a[\old(left) - 1] <= a[i]);
	  @ loop_invariant a[\old(left) - 1] <= last;
	  @ loop_invariant (\forall int i; \old(left) - 1 <= i && i < right - 1; a[i] <= a[i + 1]);
	  @ loop_invariant \old(left) <= right && right < \old(right) ==> a[right - 1] <= a[right + 1];
	  @ loop_invariant (\forall int i; right + 1 <= i && i < \old(right); a[i] <= a[i + 1]);
	  @ loop_invariant (\forall int i; right <= i && i < \old(right); last < a[i]);
	  @ loop_invariant right < \old(right) ==> a[right] <= a[right + 1];
	  @ assignable a[(\old(left))+1..(\old(right))], right;
	  @ decreases right;
	  @*/
	while (last < a[--right]) {
	    a[right + 1] = a[right];
	}

	a[right + 1] = last;
    }
}
