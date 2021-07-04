package Q2_2017;

public class MaxSumArray {
	/*
	 * Managed to show permutation property.
	 * Started working on the sortedness property, I think I was on the right track.
	 * Didn't work on termination at all.
	 * 
	 * */

	
		/*@ public normal_behaviour
	    requires 0 <= i && i < a.length;
	    requires 0 <= j && j < a.length;
	    ensures \old(a[i]) == a[j];
	    ensures \old(a[j]) == a[i];	    
	    assignable a[i], a[j];
	    @*/
	
	
	//ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
		public void swap(int[] a, int i, int j){
			int temp = a[i];
			a[i] = a[j];
			a[j] = temp;
		}
		/*@ public normal_behaviour
		    ensures (\forall int j; 0 <= j && j < a.length-1; a[j] <= a[j+1]);		    
		    diverges true;
		@*/
		//ensures \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
		public void sort(int[] a){
			
			boolean sorted = false;
			/*
			  @ loop_invariant sorted ==> (\forall int j; 0 <= j && j < a.length-1; a[j] <= a[j+1]);
			@*/
			// loop_invariant \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
			while(!sorted){
				sorted = true;
				/*@ 
				  @ loop_modifies a[*];
				  @ loop_invariant 1 <= j && (j <= a.length || a.length == 0);
				  @ loop_invariant sorted ==> (\forall int i; 0 <= i && 1 + 2 * i < j; a[2*i+1] <= a[2*i+2]);
				  
				 @*/
				// loop_invariant \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));
				for(int j = 1; j < a.length-1; j+=2){
					if(a[j] > a[j+1]){
						swap(a, j, j+1);
						sorted = false;
					}
				}
				/* @ loop_modifies a[*];
				  @ loop_invariant 0 <= k && k <= a.length;
				  @ loop_invariant sorted ==> (\forall int i; 0 <= i && 2 * i < k; a[2*i] <= a[2*i+1]) && (\forall int i; 0 <= i && 1+ 2 * i < a.length-1; a[2*i+1] <= a[2*i+2]);
				  @ loop_invariant \dl_seqPerm(\dl_array2seq(a), \old(\dl_array2seq(a)));				  
				  @*/
				for(int k = 0; k < a.length-1; k+=2){
					if(a[k] > a[k+1]){
						swap(a, k, k+1);
						sorted = false;
					}
				}
			}									
		}
	}