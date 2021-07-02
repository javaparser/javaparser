/* This demonstrates the loop_invariant_free
 * keyword, which makes it possible to assume 
 * a statement for the use case without actually 
 * proving its correctness. Like the ensures_free
 * keyword, it is unsound, so use with care.
 */
class LoopInvFree {
	static int a = 0;
	/*@
	  @ ensures a > 4;
	  @ diverges true;
	  @*/
	static void test() {
		int i = 0;
		/*@
		  @ loop_invariant_free a > 5;
		  @ assignable a;
		  @*/
		while (i < 2) {
			a++;
			i++;
		}
	}
}
