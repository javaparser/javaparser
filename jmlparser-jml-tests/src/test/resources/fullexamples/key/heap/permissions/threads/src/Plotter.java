public final class Plotter extends ThreadSpec2 {

        //@ accessible<heap> \inv : \nothing;
        //@ accessible<permissions> \inv : \nothing;

        private /*@ nullable @*/ Buffer buffer;
        private /*@ nullable @*/ AFilter ta;
        private /*@ nullable @*/ BFilter tb;

        /*@ helper model boolean preStart(Object contextThread) { return (
              \permission(this.buffer.inp) ==
                (contextThread == \dl_currentThread() ?
                   \dl_slice2(
                      \dl_owner3(ta.sampler, ta, \dl_currentThread()),
                      \dl_owner3(tb.sampler, tb, \dl_currentThread())
                   )
                 : 
                   \dl_slice2(
                      \dl_owner4(ta.sampler, ta, contextThread, \dl_currentThread()),
                      \dl_owner4(tb.sampler, tb, contextThread, \dl_currentThread())
                   )
                )
              && 
              \permission(this.buffer.outa) ==
                (contextThread == \dl_currentThread() ?
                   \dl_slice1(\dl_owner2(ta, \dl_currentThread()))
                 : 
                   \dl_slice1(\dl_owner3(ta, contextThread, \dl_currentThread()))
                )
              && 
              \permission(this.buffer.outb) ==
                (contextThread == \dl_currentThread() ?
                   \dl_slice1(\dl_owner2(tb, \dl_currentThread()))
                 : 
                   \dl_slice1(\dl_owner3(tb, contextThread, \dl_currentThread()))
                )
            ); } @*/

        /*@ helper model boolean postJoin(Object contextThread) { return true; } @*/

        /*@ helper model boolean initPost() { return (
              \dl_writePermission(\permission(this.buffer)) &&
              \dl_writePermission(\permission(this.ta)) &&
              \dl_writePermission(\permission(this.tb))
            ); } @*/

        /*@ helper model two_state boolean startTransfer() { return (
              this.ta == \old(this.ta) &&
              this.tb == \old(this.tb) &&
              this.buffer == \old(this.buffer) &&
              this.ta.sampler == \old(this.ta.sampler) &&
              this.tb.sampler == \old(this.tb.sampler) &&
              \permission(this.buffer.inp) ==
                 \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 2, \old(\permission(this.buffer.inp))) &&
              \permission(this.buffer.outa) ==
                 \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 1, \old(\permission(this.buffer.outa))) &&
              \permission(this.buffer.outb) ==
                 \dl_transferPermission(\dl_FALSE(), \dl_currentThread(), this, 1, \old(\permission(this.buffer.outb)))
            ); } @*/

        /*@ helper model two_state boolean joinTransfer() { return (
              \permission(this.buffer.inp) == 
                 \dl_returnPermission(this, \dl_currentThread(),
                    \dl_returnPermission(tb, this, 
                      \dl_returnPermission(ta, this, 
                        \dl_returnPermission(tb.sampler, tb, 
                          \dl_returnPermission(ta.sampler, ta, \old(\permission(this.buffer.inp)))
                        )
                      )
                    )
                 )
             &&
              \permission(this.buffer.outa) == 
                 \dl_returnPermission(this, \dl_currentThread(),
                    \dl_returnPermission(ta, this, \old(\permission(this.buffer.outa)))
                 )               
             &&
              \permission(this.buffer.outb) == 
                 \dl_returnPermission(this, \dl_currentThread(),
                    \dl_returnPermission(tb, this, \old(\permission(this.buffer.outb)))
                 )               
           ); } @*/

        /*@ helper model \locset workingPermissions() { return \set_union(
                 \singleton(this.buffer.inp),
                 \set_union(
                   \singleton(this.buffer.outa),
                   \singleton(this.buffer.outb) 
                 )
            ); } @*/


        /*@ helper model boolean stateInv() { return (
              buffer != null && \dl_readPermission(\permission(this.buffer)) &&
              ta != null && \dl_readPermission(\permission(this.ta)) &&
              tb != null && \dl_readPermission(\permission(this.tb)) &&
              ta.stateInv() &&
              tb.stateInv() &&
              ta.sampler == tb.sampler &&
              this.buffer == ta.buffer &&
              this.buffer == tb.buffer
            ); } @*/

        /*@ helper model \locset staticPermissions() { return \set_union(
                 \set_union(ta.staticPermissions(), tb.staticPermissions()),
                 \set_union(
                    \singleton(this.buffer),
                    \set_union(
                      \singleton(this.ta),
                      \singleton(this.tb)
                    )
                 )
            ); } @*/


        public /*@ helper @*/ void run() {
            ta.join(); // all permissions on buffer.inp from sampler -> ta -> ct
                       // all permissions on buffer.outa from ta -> ct
            tb.join(); // all permissions on buffer.inp from sampler -> ta -> ct
                       // all permissions on buffer.outa from tb -> ct
            this.buffer.inp = 0; // dummy write operation
            this.buffer.outa = 0; // dummy write operation
            this.buffer.outb = 0; // dummy write operation
        }

        /*@ normal_behavior
            requires a.stateInv();
            requires b.stateInv();
            requires a.buffer == buf;
            requires b.buffer == buf;
            requires a.sampler == b.sampler;
            ensures initPost();
            ensures this.buffer == buf;
            ensures this.ta == a;
            ensures this.tb == b;
            ensures stateInv();
            assignable \nothing;
            assignable<permissions> \nothing; @*/
        /*@ helper @*/ public Plotter(AFilter a, BFilter b, Buffer buf) {
            this.ta = a;
            this.tb = b;
            this.buffer = buf;
        }
}

