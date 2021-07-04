public class Heapify {


/*@
  requires arr.length <= 64;
 	requires 1 <= i <= len <= arr.length;
 	requires \forall int k,j; 1 < k <= Log.log2(len)-Log.log2(i) && (i<<k)<= j <=((i+1)<<k) && j<= len;arr[j-1]>= arr[(j/2)-1];
 @*/
public static void heapify(/*@ non_null @*/ int [] arr, final int i, final int len) {
	int p = i;
 	//@ assume \forall int k,j; 1 < k <= Log.log2(len)-Log.log2(p) && (p<<k)<= j <=((p+1)<<k) && j<= len;arr[j-1]>= arr[(j/2)-1];
 	//@ assert \forall int k,j; 1 < k <= Log.log2(len)-Log.log2(p) && (p<<k)<= j <=((p+1)<<k) && j<= len;arr[j-1]>= arr[(j/2)-1];
	/*@ loop_invariant i <= p <= len;
	 	loop_invariant \forall int k,j; 1 < k <= Log.log2(len)-Log.log2(p) && (p<<k)<= j <=((p+1)<<k) && j<= len;arr[j-1]>= arr[(j/2)-1];
	 	decreasing len-p;
	@*/
	while(true){
		int c = p<<1; //Left child
		
		int m = p;
		if(i <= c && c <= len && arr[c-1] < arr[m-1]) {
			m = c;
		}
		
		c++; //Right child
		if(i <= c && c <= len && arr[c-1] < arr[m-1]) {
			m = c;
		}
		
		if(m != p) {				
			int tmp = arr[p-1];
			arr[p-1] = arr[m-1];
			arr[m-1] = tmp;
		} else {
			break;
		}
		//@ assert p == m>>1;
		p = m;
		//@ assert arr[(p>>1)-1] <= arr[p-1];
	}
}

}
