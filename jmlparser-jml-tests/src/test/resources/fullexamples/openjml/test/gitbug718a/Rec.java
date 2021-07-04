public class Rec {

// This does not prove -- it seems that the solver has a limit on how 
// much it will unroll the recursive definition.

static void m(int i) {
  // @ assert countDown(0) == 0;
  // @ assert countDown(10) == 0;
  // @ assert countDown(20) == 0;
  // @ assert countDown(21) == 0;
  // @ assert countDown(25) == countDown(10);
  //@ assert countDown(25) == 0;

}

/*@
 requires c >= 0;
 ensures c == 0 ==> \result == 0;
 ensures c > 0 ==> \result == countDown(c-1);
 @*/
static /*@ pure @*/int countDown(final int c) {
	if(c > 0)
		return countDown(c-1);
	return 0;
}

/*@
 requires c >= 0;
 ensures \result == 0;
 @*/
static /*@ pure @*/int countDownA(final int c) {
	if(c > 0)
		return countDownA(c-1);
	return 0;
}

}
