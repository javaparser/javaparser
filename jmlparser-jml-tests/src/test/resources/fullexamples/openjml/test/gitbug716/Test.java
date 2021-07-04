import java.util.Arrays;
public class Test {

	/*@
	requires 0 <= l < m < r <= arr.length && arr.length > 1; //bounds
	//requires (\forall int k; l <= k && k < m;(\forall int j; k < j && j < m; arr[k] >= arr[j]));
	//requires (\forall int k; m <= k && k < r;(\forall int j; k < j && j < r; arr[k] >= arr[j]));
	//ensures \forall int k;l<= k && k < r; ( \forall int j;k < j && j < r; arr[k] >= arr[j] );
	@*/
	private static void merge(/*@ non_null @*/ int [] arr, final int l, final int m, final int r) {
		final int [] lCpy = Arrays.copyOfRange(arr, l, m),
			         rCpy = Arrays.copyOfRange(arr,m, r);
			
		//@ assert \forall int k; 0 <= k && k < lCpy.length; lCpy[k] == arr[k+l];
		//@ assert \forall int k; 0 <= k && k < rCpy.length; rCpy[k] == arr[k+m];
		
		int l1 = 0, r1 = 0;
		/*@
		 loop_invariant 0 <= l1 && l1 <= lCpy.length;
		 loop_invariant 0 <= r1 && r1 <= rCpy.length;
		 loop_invariant l <= i && i <= r;
		 loop_invariant i == l+l1+r1;
		 //loop_invariant l1 == lCpy.length ==> r1 <= rCpy.length;
		 //loop_invariant r1 == rCpy.length ==> l1 <= lCpy.length;
		 //loop_invariant \forall int k;l<= k && k < i;(\forall int j; l1 <= j && j < lCpy.length;arr[k] >= lCpy[j]);
		 //loop_invariant \forall int k;l<= k && k < i;(\forall int j; r1 <= j && j < rCpy.length;arr[k] >= rCpy[j]);
		 //loop_invariant \forall int k;l<= k && k < i; ( \forall int j;k < j && j < i; arr[k] >= arr[j] );
		 decreasing r - i;
		 @*/
		for(int i=l;i < r;) {
			if(l1 < lCpy.length && (r1 >= rCpy.length || lCpy[l1] >= rCpy[r1])) {
				arr[i++] = lCpy[l1];
				l1++;
			} else {
				arr[i++] = rCpy[r1];
				r1++;
			}
		}
	}}