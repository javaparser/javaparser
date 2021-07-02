public final class Sampler extends ThreadSpec2 {

        //@ accessible<heap> \inv : \nothing;
        //@ accessible<permissions> \inv : \nothing;

        private /*@ nullable spec_public @*/ Buffer buffer;

        /*@ helper model boolean preStart(Object contextThread) {
              return \dl_writePermissionObject(contextThread, \permission(this.buffer.inp));
            } @*/

        /*@ helper model boolean postJoin(Object contextThread) {
              return \dl_writePermissionObject(contextThread, \permission(this.buffer.inp));
            } @*/

        /*@ helper model boolean stateInv() {
              return (buffer != null && \dl_readPermission(\permission(this.buffer)));
            } @*/

        /*@ helper model boolean initPost() {
              return \dl_writePermission(\permission(this.buffer));
            } @*/

        /*@ helper model \locset workingPermissions() { return \singleton(this.buffer.inp); } @*/
        /*@ helper model \locset staticPermissions() { return \singleton(this.buffer); } @*/

        /*@ helper model two_state boolean startTransfer() {
              return \permission(this.buffer.inp) ==
                     \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 0, \old(\permission(this.buffer.inp)));
            } @*/

        /*@ helper model two_state boolean joinTransfer() { 
              return \permission(this.buffer.inp) ==
                     \dl_returnPermission(this, \dl_currentThread(), \old(\permission(this.buffer.inp)));
            } @*/

        public /*@ helper @*/ void run() {
            this.buffer.inp++; // dummy write (& read) operation
        }

        /*@ normal_behavior
            ensures initPost();
            ensures stateInv();
            ensures this.buffer == b;
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public Sampler(Buffer b) { this.buffer = b; }
}


