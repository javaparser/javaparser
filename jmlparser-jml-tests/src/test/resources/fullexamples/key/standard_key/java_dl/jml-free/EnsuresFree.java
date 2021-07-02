/* This demonstrates the ensures_free
 * keyword, which makes it possible to assume 
 * a statement in the post condition case without actually 
 * proving its correctness. It is unsound, so use with care.
 */

class EnsuresFree {
        private static int a = 0;

        /*@
          @ ensures_free a > 0;
          @*/
        static void increase() {
		a++;
        }

        /*@
	  @ ensures a > 0;
	  @*/
	static void test() {
		increase();
	}
}
