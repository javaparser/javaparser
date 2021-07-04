package sv_esc;



public class LoopExercises {

	/*@ normal_behavior
	  @ requires x != null; 
      @ requires x.length >= 1;
	  @  ensures \result == (\forall int k; 0<k && k<x.length; x[k-1] <= x[k]);
	  @*/
	boolean isOrdered(int[] x) {
		boolean result = true;
		int i = 1;

		//@ loop_invariant 1 <= i && i <= x.length;
		//@ loop_invariant result == (\forall int j; 1 <= j && j < i; x[j-1] <= x[j]);
		//@ decreasing x.length - i;
		while (result && i < x.length) {
		  result = x[i-1] <= x[i];
		  i++;
		}
		return result;
		}
	
	/*@ normal_behavior
	  @ requires 0 <= x <= Integer.MAX_VALUE/3;
	  @ ensures 2*\result == x*(x+1);
	  @*/
	public int gauss(int x) {
		int result = 0;
		int i = 1;
        //@ loop_invariant 1 <= i && i <= x + 1;
		//@ loop_invariant 2*result == (i-1)*i;
		//@ decreasing (x - i);
		while (i <= x) {
			result += i;
            //@ assert 2*result == (i-1)*i + 2*i;
	        //@ assume i*(i+1) == (i-1)*i + 2*i;
            //@ assert 2*result == i*(i+1);
			i++;
            //@ assert 2*result == (i-1)*i;
		}
		return result;
	}
	
	/*@ normal_behavior
	  @ requires x != null;
	  @ ensures (\forall int i; 0 <= i && i < x.length; x[i] <= \result);
	 */
	//@ requires x.length > 0;
	public int max(int [] x){
		int max = x[0];
		int i = 1;
        //@ loop_invariant 1 <= i && i <= x.length;
		//@ loop_invariant (\forall int j; 0 <= j && j < i; x[j] <= max);
		//@ decreasing x.length - i;
		while (i < x.length) {
			if (x[i] > max) {
				max = x[i];
			};
			i++;
		}
		return max;
	}
	
	
}
