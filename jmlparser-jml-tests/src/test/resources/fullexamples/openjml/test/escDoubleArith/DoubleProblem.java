//-@ immutable
public /*@ pure @*/ strictfp class DoubleProblem {
	
	public static void tests() {
		//@ assert 3.0 < 3.9;
		//@ assert 3.0 <= 4.0;
		//@ assert 3.02 > 3.01;
		//@ assert 3.02 != 3.01;
		//@ assert 3.02 == 3.02;
	}
}
