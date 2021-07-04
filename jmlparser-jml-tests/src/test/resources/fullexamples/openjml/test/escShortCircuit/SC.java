
public class SC {
	//@ ensures a < 0 ==> \result == 1;
	//@ ensures b < 0 ==> \result == 1;
	//@ ensures a + b < 0 ==> \result == 1;
	//@ ensures a >= 0 && b >= 0 && a+b >= 10 ==> \result == 2;
	public int m(int a, int b) {
		if(a < 0 || b < 0 || a + b < 10){
		    return 1;
		}
		return 2;

	}

	//@ ensures a < 0 ==> \result == 2;
	//@ ensures b < 0 ==> \result == 2;
	//@ ensures a + b < 0 ==> \result == 2;
	//@ ensures a >= 0 && b >= 0 && a+b >= 10 ==> \result == 1;
	public int mm(int a, int b) {
		if(a >= 0 && b >= 0 && a + b >= 10){
		    return 1;
		}
		return 2;

	}

}
