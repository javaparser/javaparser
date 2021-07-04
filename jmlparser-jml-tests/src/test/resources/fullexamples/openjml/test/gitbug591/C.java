public class C {

//@ public invariant next >= 0;
private /*@ spec_public @*/ int[] indices;
private /*@ spec_public @*/ int next;

/*@ public behavior
@ ensures \result == (\forall int x; (\forall int y; 0 <= x && x < y && y < a.length; a[x] <= a[y]));
@ assignable \nothing;
@ pure public static model boolean isSorted(int[] a);
 */

/*@ public normal_behavior
@ ensures next == 0 && this.indices == indices;
@ assignable \nothing;
@*/
public C(int[] indices) {
	this.indices = indices;
	next = 0;
}

/*@ public normal_behavior
@   requires isSorted(a);
@   ensures ((\exists int x; 0 <= x && x < a.length; a[x] == v) ?  \result >= 0 && \result < a.length && a[\result] == v : \result == -1);
@	  assignable \nothing;
@*/
public static /*@ pure @*/ int search(int[] a, int v) {
	int l = 0;
	int r = a.length - 1;

	if (a.length == 0) { 
		return -1;
	} else if (a.length == 1) { 
		return a[0] == v ? 0 : -1;
	}

	/*@ loop_invariant 0 <= l && l < r && r < a.length
    @                && (\forall int x; 0 <= x && x < l; a[x] < v)
    @                && (\forall int x; r < x && x < a.length; v < a[x]);
    @ decreases r - l;
    @*/
	while(r > l + 1) {
		int mid = l + (r - l) / 2;
		if(a[mid] == v) {
			return mid;
		} else if(a[mid] > v) {
			r = mid;
		} else {
			l = mid;
		}
	}

	if(a[l] == v) return l;
	if(a[r] == v) return r;

	return -1;
}


/*@ public normal_behavior
@ requires isSorted(a) && a != indices;
@ requires next < indices.length;
@ ensures (\exists int i; i>=0 && i<a.length; a[i] == v) ? indices[\old(next)] == \result : (next == \old(next) && indices[next] == \old(indices[next]));  
@ ensures (\exists int i; i>=0 && i<a.length; a[i] == v) ? a[\result] == v  : \result == -1;
@ assignable indices[next], next;
@ */
public int addIndex(int[] a, int v) {
	int idx = search(a,v);
	if (idx >= 0) {
		indices[next] = idx;
		next++;
	}  
	return idx;
}


/*@ 
@ public exceptional_behavior
@ requires isSorted(a);
@ requires next >= indices.length;
@ requires  (\exists int i; i>=0 && i<a.length; a[i] == v);
@ signals (ArrayIndexOutOfBoundsException) true;
@ assignable \nothing;
@*/
public int addIndex2(int[] a, int v) {
	int idx = search(a,v);
	if (idx >= 0) {
		indices[next] = idx;
		next++;
	}  
	return idx;
}
}