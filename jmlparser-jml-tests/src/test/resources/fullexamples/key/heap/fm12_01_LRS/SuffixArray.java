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

    /*@ normal_behavior
      @ ensures this.a == a;
      @*/
    public /*@ pure @*/ SuffixArray(int[] a) {
        this.a = a;
        suffixes = new int[a.length];
        /*@ maintaining 0 <= i && i <= a.length;
          @ maintaining (\forall int j; 0 <= j && j < i; suffixes[j] == j);
          @ decreasing a.length-i;
          @ assignable suffixes[*];
          @*/
        for (int i = 0; i < a.length; i++) suffixes[i] = i;
        sort(suffixes);
    }

    /*@ normal_behavior
      @ requires a != null;
      @ requires 0 <= x && x < a.length;
      @ requires 0 <= y && y < a.length;
      @ ensures \result <  0 ==>
      @           (\exists int j; 0 <= j && j < a.length-y;
      @               ((j < a.length-x && a[x+j] < a[y+j] ) || j == a.length-x)
      @               && (\forall int k; 0 <= k && k < j; a[x+k] == a[y+k]));
      @ ensures \result == 0 ==> x == y;
      @ ensures \result >  0 ==>
      @           (\exists int j; 0 <= j && j < a.length-x;
      @               ((j < a.length-y && a[x+j] > a[y+j] ) || j == a.length-y)
      @               && (\forall int k; 0 <= k && k < j; a[x+k] == a[y+k]));
      @ ensures \result == -compare(y,x);
      @ accessible a, a[*];
      @ spec_public strictly_pure helper
      @*/
    private int compare(int x, int y) {
        if (x == y) return 0;
        int l = LCP.lcp(a,x,y);

        if (x+l == a.length) return -1;
        if (y+l == a.length) return 1;
        if (a[x+l] < a[y+l]) return -1;
        if (a[x+l] > a[y+l]) return 1;

        throw new RuntimeException();
    }



    private void /*@ helper @*/ sort(final int[] data) {
        /*@ maintaining data.length == a.length;
          @ maintaining 0 <= k && k <= data.length;
          @ maintaining (\forall int i; 0 <= i && i < a.length;
          @               (\exists int j; 0 <= j && j < a.length; data[j]==i));
          @ maintaining (\forall int i; 0 < i && i < a.length;
          @                        i < k? compare(data[i],data[i-1]) > 0
          @                             : data[i] == \old(data[i]));
          @ decreasing data.length - k;
          @ assignable data[*];
          @*/
        for(int k = 0; k < data.length; k++)
            /*@ maintaining 0 <= l && l <= k;
              @ maintaining (\forall int i; l < i && i <= k;
              @                 compare(data[i],data[i-1]) > 0);
              @ maintaining (\forall int i; 0 < i && i < data.length
              @                 && !( l < i && i <= k);
              @                 data[i] == \old(data[i]));
              @ decreasing l;
              @ assignable data[*];
              @*/
            for(int l = k; l > 0 && compare(data[l - 1], data[l]) > 0; l--)
                swap(data, l);
    }

    /*@ normal_behavior
      @ requires 0 < x && x < data.length;
      @ ensures data[x]   == \old(data[x-1]);
      @ ensures data[x-1] == \old(data[x]);
      @ assignable data[x], data[x-1];
      @*/
    private static void /*@ helper @*/ swap(int[] data, int x) {
        final int y = x-1;
        final int t = data[x];
        data[x] = data[y];
        data[y] = t;
    }


}



//Based on code by Robert Sedgewick and Kevin Wayne.
