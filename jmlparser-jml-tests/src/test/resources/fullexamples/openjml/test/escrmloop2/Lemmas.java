//package q2_2012;

final class Lemmas {

    /*@ public normal_behaviour
      @  requires sa.a != null;
      @  requires 0 <= a && a < sa.a.length;
      @  requires 0 <= b && b < sa.a.length;
      @  requires 0 <= c && c < sa.a.length;
      @  requires sa.compare(a,b) > 0;
      @  requires sa.compare(b,c) > 0;
      @  ensures sa.compare(a,c) > 0;
      @  pure helper
      @*/
    public static boolean compareTrans(SuffixArray sa, int a, int b, int c) {
	return true;
    }

    /*@ public normal_behaviour
      @  requires sa.a != null;
      @  requires k > 0;
      @  requires 0 <= a && a <= sa.a.length - k;
      @  requires 0 <= b && b < sa.a.length;
      @  requires 0 <= c && c <= sa.a.length - k;
      @  requires sa.compare(a,b) >= 0;
      @  requires sa.compare(b,c) > 0;
      @  requires (\forall int t; a <= t && t < a+k; sa.a[t] == sa.a[c+t-a]);
      @  ensures  (\forall int t; a <= t && t < a+k; sa.a[t] == sa.a[b+t-a]);
      @  ensures  (\forall int t; b <= t && t < b+k; sa.a[t] == sa.a[c+t-b]);
      @  ensures  b < sa.a.length - k;
      @  pure helper
      @*/
    public static boolean compareRun(SuffixArray sa, 
					int a, int b, int c, int k){
	return true;
    }

    /*@ public normal_behaviour
      @  requires \invariant_for(sa);
      @  requires 0 <= i && i < j && j < sa.a.length;
      @  ensures sa.compare(sa.suffixes[j], sa.suffixes[i]) > 0;
      @  pure helper
      @*/
    public static boolean compareSuffixArray(SuffixArray sa, int i, int j) {

        /*@ decreases j - m;
          @ assignable \nothing;
          @ loop_invariant sa.compare(sa.suffixes[m], sa.suffixes[i]) > 0 && i+1 <= m && m <= j;
          @*/
        for(int m = i + 1; m < j; m++) {
            compareTrans(sa, sa.suffixes[m+1], sa.suffixes[m], sa.suffixes[i]);
        }
        return true;
    }

    /*@ public normal_behaviour
      @  requires sa.a != null;
      @  requires 0 <= i && i < sa.a.length;
      @  ensures sa.compare(i,i) == 0;
      @  pure helper
      @*/
    public static boolean compareReflex(SuffixArray sa, int i) {
       return true;
    }


    /*@ public normal_behaviour 
      @  requires \invariant_for(sa);
      @  requires 0 <= i && i < j && j < sa.a.length;
      @  requires
      @     sa.suffixes[i] + k <= sa.a.length &&  sa.suffixes[j] + k <= sa.a.length && 
      @     (\forall int t; 0 <=t && t < k; sa.a[sa.suffixes[i]+t] == sa.a[sa.suffixes[j]+t]);
      @  ensures
      @     sa.suffixes[i+1] + k <= sa.a.length && 
      @     (\forall int t; 0 <=t && t < k; sa.a[sa.suffixes[i]+t] == sa.a[sa.suffixes[i+1]+t]);
      @  ensures \result;
      @  pure helper
      @*/
    public static boolean neighbourMax(SuffixArray sa, int i, int j, int k) {

	compareSuffixArray(sa, i, j);
        if(j == i+1) {
            compareReflex(sa, sa.suffixes[i+1]);
        } else {
            compareSuffixArray(sa, i+1,j);
        }
	compareRun(sa, sa.suffixes[j], sa.suffixes[i+1], sa.suffixes[i], k);
        return true;
    }
}
