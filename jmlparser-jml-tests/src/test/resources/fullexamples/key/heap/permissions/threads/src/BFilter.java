public final class BFilter extends ThreadSpec2 {

        //@ accessible<heap> \inv : \nothing;
        //@ accessible<permissions> \inv : \nothing;

        private /*@ nullable spec_public @*/ Buffer buffer;
        private /*@ nullable spec_public @*/ Sampler sampler;

        /*
             (\exists nullable AFilter af; af == null || af == contextThread ||
               \permission(this.buffer.inp) ==
                   \dl_slice2(
                      \dl_owner3(sampler, af, \dl_currentThread()),
                      (contextThread == \dl_currentThread() ? 
                         \dl_owner2(sampler, \dl_currentThread())
                        :
                         \dl_owner3(sampler, contextThread, \dl_currentThread())
                      )
                   )
              )
         */

        /*@ helper model boolean preStart(Object contextThread) { return (
             \dl_readPermissionOwe2(sampler, contextThread, \permission(this.buffer.inp))
             &&
              \permission(this.buffer.outb) ==
                (contextThread == \dl_currentThread() ? 
                   \dl_slice1(\dl_owner1(\dl_currentThread()))
                 : 
                   \dl_slice1(\dl_owner2(contextThread, \dl_currentThread()))
                )
            ); } @*/

        /*@ helper model boolean postJoin(Object contextThread) {
              return true;
            } @*/ 

        /*@ helper model boolean initPost() { return (
              \dl_writePermission(\permission(this.buffer)) &&
              \dl_writePermission(\permission(this.sampler)));
            } @*/

        /*@ helper model two_state boolean startTransfer() { return (
              this.sampler == \old(this.sampler) &&
              this.buffer == \old(this.buffer) &&
              \permission(this.buffer.inp) == 
                \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 1, \old(\permission(this.buffer.inp))) &&
              \permission(this.buffer.outb) == 
                \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 0, \old(\permission(this.buffer.outb)))
            ); } @*/

        /*@ helper model two_state boolean joinTransfer() { return (
              \permission(this.buffer.inp) == 
                \dl_returnPermission(this, \dl_currentThread(),
                   \dl_returnPermission(sampler, this, \old(\permission(this.buffer.inp)))
                )
              &&
              \permission(this.buffer.outb) == 
                \dl_returnPermission(this, \dl_currentThread(), \old(\permission(this.buffer.outb)))
            ); } @*/

        /*@ helper model \locset workingPermissions() { return \set_union(
                 \singleton(this.buffer.inp),
                 \singleton(this.buffer.outb)
              ); } @*/

        /*@ helper model boolean stateInv() { return (
              buffer != null && \dl_readPermission(\permission(this.buffer)) && 
              sampler != null && \dl_readPermission(\permission(this.sampler)) && 
              sampler.stateInv() && 
              this.buffer == sampler.buffer &&
              this.sampler != \dl_currentThread()
            ); } @*/

        /*@ helper model \locset staticPermissions() { return \set_union(
                 sampler.staticPermissions(),
                 \set_union(
                    \singleton(this.buffer),
                    \singleton(this.sampler)
                 )
               ); } @*/

        public /*@ helper @*/ void run() {
            sampler.join(); // all permissions on buffer.inp from sampler to ct
            this.buffer.outb = this.buffer.inp; // dummy read & write operation
        }

        /*@ normal_behavior
            requires \dl_currentThread() != s;
            requires s.stateInv();
            requires s.buffer == b;
            ensures initPost();
            ensures this.buffer == b;
            ensures this.sampler == s;
            ensures stateInv();
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public BFilter(Sampler s, Buffer b) {
            this.sampler = s;
            this.buffer = b;
        }
}

