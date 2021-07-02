public class WhileDemo {
    public int m, i;

    /*@ public normal_behavior
      @ requires 
      @   a!=null && a.length > 0;
      @ ensures 
      @      (\forall int i; 0 <= i && i<\old(a.length); 
      @        m >= a[i]);
      @ diverges false; 
      @ */
    void findMax(int[] a) {
	i = 1; 
	m = a[0];
 
	/*@ loop_invariant  
          @ (1<=i && i<=a.length) &&
          @   (\forall int x; x>=0 && x<i; m >=a[x]);
          @
          @ assignable m,i;
	  @ decreases a.length-i;
	  @*/
      while (i<a.length) {
        if (a[i] > m )
	    m = a[i];
	i++;
      }
    }

}
