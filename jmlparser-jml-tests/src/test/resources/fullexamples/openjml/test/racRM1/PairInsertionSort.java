
package Q1_2017;
	
	public class PairInsertionSort {

	    /*@ spec_public @*/ int[] a;	    
	    
	    /*@ public behaviour	      
	      @ requires 0 < l && l <= r && r < a.length;
	      @ assignable a[*];
	      @ ensures (\forall int i; l <= i && i < r; a[i] <= a[i + 1]);
	      @*/
	    public void sort(int l, int r) {
			int left = l;
			int right = r;

			/*@ loop_modifies a[*];
			  @ decreases right + 1 - left; 
			  @ loop_invariant l <= k && k <= right;
			  @ loop_invariant l <= left && left <= right + 1 && right == r;
			  @ loop_invariant (\forall int i; l <= i && i < left; a[i] <= a[i + 1]);
			  @*/
			for (int k = left; ++left <= right; k = ++left) 
				{
			    int a1 = a[k];
			    int a2 = a[left];
			    if (a1 < a2) {
				a2 = a1; a1 = a[left];
			    }
		    
		    /*@ 
		      @ loop_modifies a[*];
		      @ decreases k;
		      @ loop_invariant l <= k && k < r;
		      @ loop_invariant (\forall int i; l <= i && i < k-1; a[i] <= a[i + 1]);
		      @*/
			    
		    while (a1 < a[--k]) {
			a[k + 2] = a[k];
		    }
		    a[++k + 1] = a1;
		    
		    /*@ 
		      @ loop_modifies a[*];
		      @ decreases k;
		      @ loop_invariant l <= k && k < r;
		      @ loop_invariant (\forall int i; l <= i && i < k-1; a[i] <= a[i + 1]);
		      @*/
		    while (a2 < a[--k]) {
			a[k + 1] = a[k];
		    }
		    a[k + 1] = a2;
		}
		int last = a[right];
		/*@ 
		  @ loop_modifies a[*];
		  @ decreases right;
		  @ loop_invariant l <= right && right < r;
		  @ loop_invariant right <= left + 1;
		  @ loop_invariant (\forall int i; right <= i && i <= r; last <= a[i]);
		  @ loop_invariant (\forall int i; l <= i && i < right - 1; a[i] <= a[i + 1]);
		  @ loop_invariant (\forall int i; right < i && i < r-1; a[i] <= a[i + 1]);
		  @*/
		while (last < a[--right]) {
		    a[right + 1] = a[right];
		}
		a[right + 1] = last;	    
	}
}