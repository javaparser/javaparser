public class Sqrt {
    //@ spec_public
	double precision = 0.0001;

	//@ ghost public static double eps = 0.00001;

    /*@
      requires x >= 0.0 && precision > 0;
      //ensures org.jmlspecs.models.JMLDouble.approximatelyEqualTo(x, \result * \result, eps);
    */
	public double sqrt(double x) {
		double a = 0, b = x+1, m = 0;
		//@ loop_invariant b >= m && m >= a && a >= 0;
		//@ loop_invariant b*b >= x && x >= a*a;
		//@ loop_invariant b == m || a == m;
		while (b*b - a*a > precision) {
			m = (b + a) / 2;
			if (m * m > x) {
				b = m;
			}
			else {
				a = m;
			}
		}
		// Some but likely not all of these asserts needed as lemmas
		//@ assert b*b >= x && x >= a*a && b >= a && a >= 0;
        //@ assert b == m || a == m;
        //@ assert b*b - a*a <= precision;
        //@ assert b*b - x <= b*b - a*a;
        //@ assert x - a*a <= b*b - a*a;
        //@ assert b*b - x <= precision;
        //@ assert x - a*a <= precision;
        //@ assert m*m >= x ==> 0 <= m*m - x <= precision;
        //@ assert m*m <= x ==> -precision <= m*m - x <= 0;
		// Conclusion:
		//@ assume !Double.isNaN(m*m - x);
        //@ assert -precision <= m*m - x <= precision;
		return m;
	}
}