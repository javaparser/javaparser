public class TwoWaySwap {

    private boolean[] a;
    //@ model \seq seq;
    //@ represents seq = \dl_array2seq(a);


    /*@ public normal_behavior
      @ ensures a == _a;
      @ modifies a;
      @*/
    public void set(boolean[] _a) {
	a = _a;
    }

    /*@ public normal_behavior
      @ requires i >= 0 && i<a.length &&  j >= 0 && j<a.length;
      @ ensures a[i] == \old(a[j]) && a[j] == \old(a[i]);
      @ ensures seq == \dl_seqSwap(\old(seq), i, j);
      @ assignable a[i], a[j];
      @*/
    public void swap(int i,int j) {
	boolean t = a[i];
	a[i] = a[j];
	a[j] = t;
    }

    /*@ public normal_behavior
      @ ensures (\forall int k; 
      @   (\forall int l; k>=0 && k < l && l<a.length; a[k] == a[l] || !a[k]));
      @ ensures \dl_seqPerm(\old(seq), seq);
      @ assignable a[*];
      @*/
    public void twoWaySort() {
	int i = 0;
	int j = a.length - 1;
	/*@ loop_invariant
	  @   i>=0 && j < a.length && j-i >= -1 &&
	  @   (\forall int m; m>=0 && m<i; !a[m]) &&
	  @   (\forall int m; m>j && m<a.length; a[m]) &&
	  @   (\forall int m; m>=i && m <=j; a[m] == \old(a[m])) &&
	  @   \dl_seqPerm(\old(seq), seq);
	  @ assignable a[*];
	  @ decreases j - i + 1;
	  @*/
	while (i <= j) {
	    if (!a[i]) {
		i = i+1;
	    } else if (a[j]) {
		j = j-1;
	    } else {
		swap(i, j);
		i = i+1;
		j = j-1;
	    }
	}
    }
}