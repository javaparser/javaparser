// This is Challenge 1A from the 2019 VerifyThis competition
// a[] is a sequence of integers
// need to compute a result cut that marks the bounds of monotonic sequences within a (either monotonically decreasing or (= or inccreasing))
// begin-to-end property   cut[0] == 0 && cut[cut.length-1] == a.length
// in-range   i in 0 .. cut.length-1   0 <= cut[i] <= a.length
// increasing i in 0 .. cut.length-2   cut[i] < cut[i+1]
// monotonic  i in 0 .. cut.length-2   a[cut[i]..cut[i+1]-1] is monotonic 
// maximal    i in 1 .. cut.length-1   a[
public class Challenge1A {
    
    //@ public normal_behavior
	//@ requires a.length >= 1;
    //@ assigns \nothing;
    //@ ensures \result.length <= a.length/2 + 2; // non-empty
    //@ ensures \result[0] == 0 && \result[\result.length-1] == a.length; // begin-to-end
    //@ ensures \forall int i; 0 <= i < \result.length; 0 <= \result[i] <= a.length; // within-bounds
    // @ ensures \forall int i,j; 0 <= i < \result.length-1 && \result[i] <= j < \result[i+1] - 1; a[\result[i]] < a[\result[i]+1] <==> a[j] < a[j+1]; // monotonic
    // @ ensures \forall int i; 0 <= i < \result.length-1; \result[i+1] < a.length ==> (a[\result[i]] < a[\result[i]+1] <=!=> a[\result[i+1]-1] < a[\result[i+1]]); // maximal
    // @ ensures \forall int i; 0 <= i < \result.length-1; \result[i] > 0 ==> (a[\result[i]] < a[\result[i]+1] <=!=> a[\result[i]-1] < a[\result[i]]); // maximal
    public int[] findMonotonicCutpoints(int[] a) {
        
        int[] cut = new int[a.length/2+2];
        cut[0] = 0;
        int lengthcut = 1;
        int x = 0;
        int y = 1;
        int n = a.length;
        //@ loop_invariant 1 <= y <= (x<n?n:n+1);
        //@ loop_invariant 0 < lengthcut < y/2+2;
        //@ loop_invariant cut[0] == 0; // begin-to-end so far
        //@ loop_invariant y == x+1; // initial conditions for modified variables
        //@ loop_invariant x == cut[lengthcut-1]; // initial conditions for modified variables
        //@ loop_invariant \forall int i; 0 <= i < lengthcut; 0 <= cut[i] <= y; // within bounds so far
        //@ loop_invariant \forall int i,j; 0 <= i < lengthcut-1 && cut[i] <= j < cut[i+1] - 1; a[cut[i]] < a[cut[i]+1] <==> a[j] < a[j+1]; // monotonic so far
        // @ loop_invariant \forall int i; 0 <= i < lengthcut-1; cut[i+1] < a.length ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i+1]-1] < a[cut[i+1]]); // maximal so far
        // @ loop_invariant \forall int i; 0 <= i < lengthcut-1; cut[i] > 0 ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i]-1] < a[cut[i]]); // maximal so far
        // @ loop_invariant x > 0 ==> (a[x] < a[x+1] <=!=> a[x-1] < a[x]); // last segment maximal so far
        //@ loop_writes x, y, lengthcut, cut[*];
        //@ loop_decreases n - y;
        while (y<n) {
            // @ assume \forall int i; 0 <= i < lengthcut-1; cut[i] > 0 ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i]-1] < a[cut[i]]); // maximal so far
            // @ assume x > 0 ==> (a[x] < a[x+1] <=!=> a[x-1] < a[x]); // last segment maximal so far

            boolean increasing = a[x] < a[y];
            //@ loop_invariant x < y <= n;  // initial conditions for modified variables
            //@ loop_invariant 0 < lengthcut < y/2+2;
            //@ loop_invariant \forall int i; 0 <= i < lengthcut; 0 <= cut[i] <= y; // within bounds so far
            //@ loop_invariant \forall int j; x <= j < y-1; (a[x] < a[x+1] <==> a[j] < a[j+1]); // last segment monotonic so far
            //@ loop_writes y;
            //@ loop_decreases n - y;
            while (y < n && (a[y-1] < a[y] == increasing)) y = y + 1;
            // @ assert \forall int i; 0 <= i < lengthcut-1; cut[i] > 0 ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i]-1] < a[cut[i]]); // maximal so far
            cut[lengthcut++] = y;
            //@ assert \forall int i; 0 <= i < lengthcut; 0 <= cut[i] <= y; // within bounds so far
            x = y;
            y = x + 1;

            // @ assert \forall int i; 0 <= i < lengthcut-1; cut[i] > 0 ==> (a[cut[i]] < a[cut[i]+1] <=!=> a[cut[i]-1] < a[cut[i]]); // maximal so far
        }
        if (x < n) {
            cut[lengthcut++] = n;
        }
        int[] newcut = new int[lengthcut];
        System.arraycopy(cut, 0, newcut, 0, lengthcut);
        return newcut;
    }
}