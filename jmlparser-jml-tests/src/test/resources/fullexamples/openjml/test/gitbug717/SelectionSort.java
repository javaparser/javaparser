public class SelectionSort {

  // Sorts the first n elements of the array in descending order

// FIXME - the permutation tracking does not yet work

  //@ requires 1 <= n <= A.length;
  //@ ensures \forall int k; 0 <= k < n-1; A[k] >= A[k+1];
  public static void sort(int[] A, int n) {
    //@ ghost int[] perm = new int[n];
    //@ ghost int[] rev = new int[n];
    //@ havoc perm[*]; assume \forall int z; 0 <= z < n; z == perm[z];
    //@ havoc rev[*]; assume \forall int z; 0 <= z < n; z == rev[z];
    //@ assert \forall int z; 0 <= z < n; z == rev[perm[z]];
    //@ assert \forall int z; 0 <= z < n; z == perm[rev[z]];
    //@ assert \forall int z; 0 <= z < n; \old(A[z]) == A[perm[z]];

    //@ loop_invariant 0 <= i < n;
    //@ loop_invariant \forall int k; 0 <= k < i; A[k] >= A[k+1]; 
    //@ loop_invariant \forall int k; 0 <= k < i; \forall int j; i <= j < n; A[k] >= A[j]; 
    //@ decreasing n - i - 1;
    //@ loop_invariant \forall int z; 0 <= z < n; 0 <= perm[z] < n;
    //@ loop_invariant \forall int z; 0 <= z < n; 0 <= rev[z] < n;
    //@ loop_invariant \forall int z; 0 <= z < n; z == rev[perm[z]];
    //@ loop_invariant \forall int z; 0 <= z < n; z == perm[rev[z]];
    //@ loop_invariant \forall int z; 0 <= z < n; \old(A[z]) == A[perm[z]];

    for(int i = 0; i < n - 1; i++) {
      int max = A[i];
      int max_idx = i;
	
      //@ loop_invariant i < j <= n; 
      //@ loop_invariant \forall int t; i <= t < j; max >= A[t]; 
      //@ loop_invariant i <= max_idx < n; 
      //@ loop_invariant max == A[max_idx]; 
      //@ decreasing n - j; 
      for(int j = i+1; j < n ;j++) {
        if (A[j] > max) {
          max_idx = j;
          max = A[j];
        }
      }
      A[max_idx] = A[i];
      A[i] = max;
      //@ set perm[rev[max_idx]] = i;
      //@ set perm[rev[i]] = max_idx;
      //@ set rev[max_idx] = i;
      //@ set rev[i] = max_idx;
    }
    //@ assert perm.length == n;
    //@ assert rev.length == n;
    //@ assert \forall int z; 0 <= z < n; 0 <= perm[z] < n;
    //@ assert \forall int z; 0 <= z < n; 0 <= rev[z] < n;
    // @ assert \forall int z; 0 <= z < n; z == rev[perm[z]];
    // @ assert \forall int z; 0 <= z < n; z == perm[rev[z]];
    //@ assert \forall int i; 0 <= i < n; \old(A[i]) == A[perm[i]];
  }
}
