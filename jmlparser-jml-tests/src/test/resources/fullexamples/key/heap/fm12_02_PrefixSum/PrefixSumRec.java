final class PrefixSumRec {

    private final int[] a;
    
    //@ invariant a.length > 0;
    //@ invariant isPow2(a.length);
    //@ accessible \inv: \singleton(a);
    
    //@ axiom evenSumLemma();

    PrefixSumRec(int [] a) {
	this.a = a;
    }

    /*@ normal_behavior
      @   ensures \result == (\forall int x, y; even(x) == (even(y) == even(x+y)));
      @   ensures \result;
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean evenSumLemma() { return true; }

    /*@ public normal_behavior
      @   requires x > 0;
      @   ensures \result ==> ((even(x)  && isPow2(div2(x))) <=!=> x == 1);
      @   ensures \result == (\exists int b; 0 <= b;
      @                     x == (\product int i; 0 <= i && i < b; 2));
      @   measured_by x;
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean isPow2(int x){
      if (x==1) 
          return true;
      else if (x % 2 != 0 ) 
          return false;
      else 
          return isPow2(x/2);
    } 

    /*@ normal_behavior
      @   requires x >= 0;
      @   ensures \result == (\product int i; 0 <= i && i < x; 2);
      @   ensures \result > x;
      @   accessible \nothing;
      @   measured_by x;
      @ strictly_pure helper
      @*/
    private static int pow2( int x ) {
      return x==0? 1: 2*pow2(x-1);
    }

    /*@ normal_behavior
      @   requires x > 0;
      @   requires even(x);
      @   ensures \result*2 == x;
      @   ensures \result == x/2;
      @   ensures \result < x;
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static int div2 (int x) {
        return x/2;
    }
    
    /*@ normal_behavior
      @   ensures \result == (\exists int y; y*2 == x);
      @   ensures \result != (\exists int y; y*2 == x+1);
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static boolean even (int x) {
        return x%2==0;
    }

    //@ strictly_pure
    private /*@ helper @*/ static int leftMost(int left, int right) {
	return 2*left - right + 1;
    }

    /*@ normal_behavior
      @   requires k >= 0;
      @   ensures 0 <= \result && \result <= k;
      @   ensures pow2(\result) <= k+1;
      @   ensures k% pow2(\result+1) == pow2(\result)-1;
      @   ensures (\forall int z; k% pow2(z+1) == pow2(z)-1; 
      @               z >= \result);
      @   accessible \nothing;
      @ strictly_pure helper
      @*/
    private static int min ( int k ) {
        int n = 0;
        /*@ maintaining (\forall int z; 0 <= z && z < n;
          @                 k% pow2(z+1) != pow2(z)-1 );
          @ maintaining 0 <= n && pow2(n) <= k+1;
          @ decreasing k-n+1;
          @ assignable \strictly_nothing;
          @*/
        while ( k% pow2(n+1) != pow2(n)-1 ) n++;
        return n;
    }

    /*@ normal_behavior
      @   requires 0 <= k;
      @   ensures \result == pow2(min(k));
      @   ensures 0 < \result && \result <= k+1;
      @   measured_by k + 2;
      @   accessible \nothing;
      @*/
    private /*@ helper strictly_pure @*/ static int f ( int k ) {
        return even(k)? 1: f(div2(k-1));
    }


    /*@ public normal_behavior
      @   requires right > left;
      @   requires leftMost(left, right) >= 0;
      @   requires right < a.length;
      @   requires isPow2(right-left);
      @   requires !even(right);
      @   requires !even(left) || right-left==1;
      @   ensures (\forall int k; 0 <= k && k < 2*(right-left);
      @            a[k+leftMost(left,right)] == (\sum int i; k-f(k)+1 <= i && i < k+1; \old(a[i+leftMost(left,right)])));
      @   //ensures a[right] == (\sum int i; leftMost(left,right) <= i && i < right+1; \old(a[i])); // the simple side-condition
      @   measured_by right - left + a.length + 3;
      @   assignable (\infinite_union int k; leftMost(left,right) <= k
      @              && k <= right && !even(k); \singleton(a[k]));
      @*/
public void upsweep(int left, int right) {
    int space = right - left;
    if (space > 1) {
        upsweep(left - div2(space), left);
        upsweep(right - div2(space), right);
    }
    a[right] = a[left] + a[right];
}

    private static int binWeight (int i) {
        if (i==0) return 0;
        if (even(i)) return binWeight(div2(i));
        return 1 + binWeight(div2(i-1));
    }

    /*@ normal_behavior
      @   requires right > left;
      @   requires leftMost(left, right) >= 0;
      @   requires right < a.length;
      @   requires isPow2(right-left);
      @   requires !even(right);
      @   requires !even(left) || right-left==1;
      @// ensures (\forall int k; leftMost(left,right) <= k && k <= right;
      @//             a[k] == (\sum int i; 0 <= i && i < binWeight(k-leftMost(left,right)); \old(a[i+leftMost+xxx])) + \old(a[right]));
      @   measured_by right - left + a.length + 3;
      @   assignable (\infinite_union int k; leftMost(left,right) <= k
      @                              && k <= right; \singleton(a[k]));
      @*/
    public void downsweep(int left, int right) {
        int tmp = a[right];
        a[right] = a[right] + a[left];
        a[left] = tmp;
        int space = right - left;
        if (space > 1) {
            downsweep(left-div2(space),left);
            downsweep(right-div2(space),right);
        }
    }
    
    /*@ normal_behavior
      @   requires \invariant_for(p) && p.a.length > 1;
      @   ensures (\forall int i; 0 <= i && i < p.a.length;
      @             p.a[i] == (\sum int j; 0 <= j && j < i;
      @                           \old(p.a[i])));
      @*/
    public static void main( PrefixSumRec p ) {
        final int l = div2(p.a.length)-1;
        final int r = p.a.length-1;
        p.upsweep(l, r);
        p.a[r] = 0;
        p.downsweep(l, r);
    }
}
