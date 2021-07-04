//package q2_2012;

public final class SuffixArray {

    final /*@ spec_public @*/ int[] a;
    final /*@ spec_public @*/ int[] suffixes;

    /*@ public invariant 
      @           (\forall int i; 0 <= i && i < a.length; 
      @           (\exists int j; 0 <= j && j < a.length; suffixes[j]==i));
      @           // suffixes is a permutation on indices
      @ public invariant
      @         (\forall int i; 0 <= i && i < a.length;
      @                  0 <= suffixes[i] && suffixes[i] < a.length);
      @           // indices are in range (follows from above, cannot hurt)
      @ public invariant (\forall int i; 0 < i && i < a.length; 
      @                        suffixes[i-1] != suffixes[i]);
      @           // indices are unique (follows from above, cannot hurt)
      @ public invariant (\forall int i; 0 < i && i < a.length; 
      @                        compare(suffixes[i],suffixes[i-1]) > 0);
      @           // suffixes is ordered lexicographically
      @ public invariant a.length == suffixes.length;
      @*/

    /*@ public normal_behavior
      @ ensures this.a == a;
      @*/
    //@ skipesc // Various proof failures
    public /*@ pure @*/ SuffixArray(int[] a) {
        this.a = a;
        suffixes = new int[a.length];
        /*@ loop_modifies suffixes[*];
          @ maintaining 0 <= i && i <= a.length;
          @ maintaining (\forall int j; 0 <= j && j < i; suffixes[j] == j);
          @ decreasing a.length-i;         
          @*/
        for (int i = 0; i < a.length; i++) suffixes[i] = i;
        sort(suffixes);
    }

    /*@ normal_behavior
      @ requires a != null;
      @ requires 0 <= x && x < a.length;
      @ requires 0 <= y && y < a.length;
      @ ensures \result <  0 <==>
      @           (\exists int j; x <= j && j < a.length-y+x;
      @               ((j < a.length && a[j] < a[y+j-x] ) || j == a.length)
      @               && (\forall int k; x <= k && k < j; a[k] == a[k-x+y]));
      @ ensures \result == 0 <==> x == y;
      @ ensures \result >  0 <==>
      @           (\exists int j; x <= j && j < a.length;
      @               ((j < a.length-y+x && a[j] > a[y+j-x] ) || j == a.length-y+x)
      @               && (\forall int k; x <= k && k < j; a[k] == a[k-x+y]));
      @ // ensures \result == -compare(y,x);
      @ accessible a, a[*];
      @ spec_public pure helper
      @*/
    //@ skipesc // Various proof failures
    private int compare(int x, int y) {
        if (x == y) return 0;
        int l = LCP.lcp(a,x,y);

        if (x+l == a.length) return -1;
        if (y+l == a.length) return 1;
        if (a[x+l] < a[y+l]) return -1;
        if (a[x+l] > a[y+l]) return 1;
        
        throw new RuntimeException();
    }


    //@ private normal_behavior
    //@   assignable data[*];
    //@   ensures (\forall int k; 0 < k && k < data.length; data[k] >= data[k-1]);
    //@ skipesc // Various proof failures
    private /*@ helper @*/ void sort(final int[] data) {
       /* @ //assignable data[*];
          @ maintaining data.length == a.length;
          @ maintaining 0 <= k && k <= data.length;
          @ maintaining (\forall int i; 0 <= i && i < a.length; 
          @               (\exists int j; 0 <= j && j < a.length; data[j]==i));
          @ maintaining (\forall int i; 0 < i && i < a.length; 
          @                        i < k? compare(data[i],data[i-1]) > 0
          @                             : data[i] == \old(data[i]));
          @ decreasing data.length - k;         
          @*/
        for(int k = 0; k < data.length; k++) 
           /*@ loop_modifies data[*];
              @ maintaining 0 <= l && l <= k;
              @ maintaining (\forall int i; l < i && i <= k;
              @                 compare(data[i],data[i-1]) > 0);
              @ maintaining (\forall int i; 0 < i && i < data.length
              @                 && !( l < i && i <= k);
              @                 data[i] == \old(data[i]));
              @ decreasing l;              
              @*/
            for(int l = k; l > 0 && compare(data[l - 1], data[l]) > 0; l--) 
                swap(data, l);
    }

    /*@ private normal_behavior
      @ requires 0 < x && x < data.length;
      @ ensures data[x] == \old(data[x-1]);
      @ ensures data[x-1] == \old(data[x]);
      @ assignable data[x], data[x-1];
      @*/
    private /*@ helper @*/ static void  swap(int[] data, int x) {
        final int y = x-1;
        final int t = data[x];
        data[x] = data[y];
        data[y] = t;
    }


}



//Based on code by Robert Sedgewick and Kevin Wayne.
