public class Fib extends ThreadSpec {

        //@ accessible<heap> \inv : \nothing;
        //@ accessible<permissions> \inv : \nothing;

        private int number;

        /*@ helper model boolean preStart(Object contextThread) {
              return \dl_writePermissionObject(contextThread, \permission(this.number));
            } @*/

        /*@ helper model boolean postJoin(Object contextThread) {
              return \dl_writePermissionObject(contextThread, \permission(this.number));
            } @*/

        /*@ helper model boolean initPost() {
              return \dl_writePermission(\permission(this.number));
            } @*/

        /*@ helper model \locset workingPermissions() {
              return \singleton(this.number);
            } @*/

        /*@ helper model two_state boolean startTransfer() {
              return \permission(this.number) ==
                \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 0, \old(\permission(this.number)));
            } @*/

        /*@ helper model two_state boolean joinTransfer() { 
              return \permission(this.number) ==
                \dl_returnPermission(this, \dl_currentThread(), \old(\permission(this.number)));
            } @*/

        public /*@ helper @*/ void run() {
            if(number >= 2) {
                Fib f1 = new Fib(number - 1);
                Fib f2 = new Fib(number - 2);
                f1.start();
                f2.start();
                f1.join();
                f2.join();
                number = f1.number + f2.number;
          }
        }

        /*@ normal_behavior
            ensures \dl_writePermission(\permission(this.canJoin));
            ensures initPost();
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public Fib(int n) { this.number = n; }
}
