/**
 * Taken from the paper
 *    "Reasoning about Comprehensions with First-Order SMT Solvers" 
 * and
 *    "Automatic verification of textbook programs that use comprehensions"
 * 
 * both by Rustin Leino and Rosemary Monahan
 */
public class Sum {


    /*@ public normal_behaviour 
      @ ensures result == (\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum0(int[] a) {
	int s = 0;
	/*@ loop_invariant
	  @   0<=n && n<=a.length && s == (\bsum int i; 0; n; a[i]);
	  @ assignable \nothing;
	  @ decreases a.length-n;
	  @*/
	for (int n = 0; n < a.length; n++) {
	    s += a[n]; 
	}	
	return s; 
    }


    /*@ public normal_behaviour 
      @ ensures result == (\bsum int i; 0; a.length; a[i]);
      @*/
    public static int sum1(int[] a) {
	int s = 0;
	/*@ loop_invariant
	  @   0<=n && n<=a.length &&
	  @   s + (\bsum int i; n; a.length; a[i]) ==  (\bsum int i; 0; a.length; a[i]);
	  @ assignable \nothing;
	  @ decreases a.length-n;
	  @*/
	for (int n = 0; n < a.length; n++) {
	    s += a[n]; 
	}	
	return s; 
    }


    /*@ public normal_behaviour 
      @ ensures result == (\sum int i; 0<=i  && i<a.length; a[i]);
      @*/
    public static int sum2(int[] a) {
	int s = 0;
	/*@ loop_invariant 0<=n && n<=a.length &&
	  @  s == (\sum int i; n <= i && i<a.length; a[i]);
	  @ assignable \nothing;
	  @ decreases n + 1;
	  @*/
	for (int n = a.length; 0 <= --n; ) {
	    s += a[n]; 
	} 
	return s;
    }


    /*@ public normal_behaviour 
      @ ensures result == (\sum int i; 0<=i  && i<a.length; a[i]);
      @*/
    public static int sum3(int[] a) {
	int s = 0;
	/*@ loop_invariant 0<=n && n<=a.length &&
	  @  s + (\sum int i; 0 <= i && i < n; a[i]) == (\sum int i; 0<=i  && i<a.length; a[i]);
	  @ assignable \nothing;
	  @ decreases n + 1;
	  @*/
	for (int n = a.length; 0 <= --n;) {
	    s += a[n]; 
	} 
	return s;
    }

}