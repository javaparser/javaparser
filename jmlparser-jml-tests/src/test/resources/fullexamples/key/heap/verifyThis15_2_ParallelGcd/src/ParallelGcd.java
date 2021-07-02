public class ParallelGcd {

	/*@ public model_behavior
	  @ requires 0 < a && 0 < b;
	  @ ensures 0 < \result && (a % \result == 0) && (b % \result == 0)
	  @ && !(\exists int i; 0 < i && i <= a && \result < i; (a % i == 0) && (b % i == 0))
	  @ && (a == b ==> (\result == a))
	  @ && (a < b ==> (\result == gcd(a, b - a)))
	  @ && (b < a ==> (\result == gcd(a - b, b)));
	  @ assignable \strictly_nothing;
	  @ public static model two_state int gcd(int a, int b);
	*/

	/*@ public behavior
	  @ requires 0 < aIn && 0 < bIn;
	  @ assignable \nothing;
	  @ ensures 0 < \result && (\result == gcd(aIn, bIn));
	  @ signals (Exception e) true;
	  @*/
	public static int parallelGcd(final int aIn, final int bIn, final boolean[] r) throws Exception {
		int a = aIn;
		int b = bIn;
		int i = 0;

		/*@ loop_invariant 0 <= i
		  @ && 0 < a && 0 < b
		  @ && gcd(a, b) == gcd(aIn, bIn)
		  @ && (b < a ==> (gcd(a, b) == gcd(a - b, b)))
		  @ && (a < b ==> (gcd(a, b) == gcd(a, b - a)));
		  @ assignable \nothing;
		  @ decreases r.length - i;
		  @*/
		while(a != b) {
			if (r.length <= i) {
				throw new Exception();
			}
			if (r[i]) {
				if (a > b) { a = a - b; }
			} else {
				if (b > a) { b = b - a; }
			}
			i++;
		}
		return a;
	}
}