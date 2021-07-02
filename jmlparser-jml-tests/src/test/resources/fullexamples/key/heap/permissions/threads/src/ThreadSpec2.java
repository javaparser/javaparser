public class ThreadSpec2 {

        /*@ model_behavior 
          requires stateInv();
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> workingPermissions();
          helper model boolean preStart(Object contextThread); @*/

        /*@ model_behavior 
          requires stateInv();
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> workingPermissions();
          helper model boolean postJoin(Object contextThread); @*/

        /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> staticPermissions();
          helper model boolean stateInv(); @*/

        /*@ model_behavior 
          requires true;
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> \set_union(staticPermissions(), workingPermissions());
          helper model boolean initPost() { return true; } @*/

        /*@ model_behavior 
          requires stateInv();
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> \nothing;
          helper model \locset workingPermissions(); @*/

        /*@ model_behavior 
          requires stateInv();
          ensures true;
          accessible<heap> staticPermissions();
          accessible<permissions> \nothing;
          helper model \locset staticPermissions(); @*/


        /*@ model_behavior 
          requires stateInv();
          ensures \result ==> (\old(preStart(\dl_currentThread())) ==> preStart(this));
          accessible<heap> staticPermissions();
          accessible<heapAtPre> staticPermissions();
          accessible<permissionsAtPre> workingPermissions();
          accessible<permissions> workingPermissions();
          helper model two_state boolean startTransfer(); @*/

        /*@ model_behavior 
          requires stateInv();
          ensures \result ==> (\old(postJoin(this)) ==> postJoin(\dl_currentThread()));
          accessible<heap> staticPermissions();
          accessible<heapAtPre> staticPermissions();
          accessible<permissionsAtPre> workingPermissions();
          accessible<permissions> workingPermissions();
          helper model two_state boolean joinTransfer(); @*/


        /*@ normal_behavior
            requires this != \dl_currentThread();
            requires preStart(\dl_currentThread());
            requires stateInv();
            ensures startTransfer();
            assignable<permissions> workingPermissions();
            assignable<heap> \nothing; @*/
        public /*@ helper @*/ native void start();

        /*@ normal_behavior
            requires this != \dl_currentThread();
            requires stateInv();
            ensures joinTransfer();
            assignable<permissions> workingPermissions();
            assignable<heap> workingPermissions(); @*/
        public /*@ helper @*/ native void join();

        /*@ normal_behavior
            requires this == \dl_currentThread();
            requires preStart(this);
            requires stateInv();
            ensures stateInv();
            ensures postJoin(this);
            assignable<heap> workingPermissions();
            assignable<permissions> workingPermissions(); @*/
        public /*@ helper @*/ void run() {}

        /*@ normal_behavior
            ensures initPost();
            ensures stateInv();
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public ThreadSpec2() {}
}
