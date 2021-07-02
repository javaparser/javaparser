public class ThreadSpec {

      /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> \nothing;  // ??? footprint()?
          accessible<permissions> workingPermissions();
          helper model boolean preStart(Object contextThread); @*/

      /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> \nothing;  // ??? footprint()?
          accessible<permissions> workingPermissions();
          helper model boolean postJoin(Object contextThread); @*/

      /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> workingPermissions();
          accessible<permissions> workingPermissions();
          helper model boolean initPost() { return true; } @*/

      /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> \nothing;
          accessible<permissions> \nothing;
          helper model \locset workingPermissions(); @*/

      /*@ model_behavior 
          requires true;
          ensures \result ==> (\old(preStart(\dl_currentThread())) ==> preStart(this));
          accessible<heap> \nothing;
          accessible<heapAtPre> \nothing;
          accessible<permissionsAtPre> workingPermissions();
          accessible<permissions> workingPermissions();
          helper model two_state boolean startTransfer(); @*/

      /*@ model_behavior 
          requires true;
          ensures \result ==> (\old(postJoin(this)) ==> postJoin(\dl_currentThread()));
          accessible<heap> \nothing;
          accessible<heapAtPre> \nothing;
          accessible<permissionsAtPre> workingPermissions();
          accessible<permissions> workingPermissions();
          helper model two_state boolean joinTransfer(); @*/


        /*@ normal_behavior
            requires this != \dl_currentThread();
            requires true;
            requires preStart(\dl_currentThread());
            ensures startTransfer();
            assignable<permissions> workingPermissions();
            assignable<heap> \nothing; @*/
        public /*@ helper @*/ native void start();

        /*@ normal_behavior
            requires this != \dl_currentThread();
            requires \dl_readPermission(\permission(this.canJoin)); 
            ensures postJoin(\dl_currentThread());
            ensures joinTransfer();
            assignable<permissions> workingPermissions();
            assignable<heap> workingPermissions(); @*/
        public /*@ helper @*/ native void join();

        /*@ normal_behavior
            requires this == \dl_currentThread();
            requires preStart(this);
            ensures postJoin(this);
            assignable<heap> workingPermissions();
            assignable<permissions> \nothing; @*/
        public /*@ helper @*/ void run() {}

        //@ public instance ghost boolean canJoin;

        /*@ normal_behavior
            ensures \dl_writePermission(\permission(this.canJoin));
            ensures initPost();
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public ThreadSpec() {}
}
