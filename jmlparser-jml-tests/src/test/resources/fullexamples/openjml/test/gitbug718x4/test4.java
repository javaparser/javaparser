
public class test4 {
	/*@
	 requires c >= 0;
	 ensures c > 0 ==> \result == countDown(c-1);
	 ensures c == 0 ==> \result == 0;
	 @*/
	static /*@ pure @*/int countDown(final int c) {
		if(c > 0)
			return countDown(c-1);
		return 0;
	}
	
	public static void test() {
		//@ assert countDown(20) == 0;
		//@ assert countDown(42) == 0;
		//@ assert countDown(50) == 0;

		//@ assert \forall int k; 0 <= k <= 50; countDown(k)==0;
	}
}
