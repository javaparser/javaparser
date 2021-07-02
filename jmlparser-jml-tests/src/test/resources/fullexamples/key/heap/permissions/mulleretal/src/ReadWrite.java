public class ReadWrite {

    //@ accessible<heap> \inv : \nothing;
    //@ accessible<permissions> \inv : \nothing;

    private int val;

    /*@ public normal_behavior
          requires \dl_writePermission(\permission(this.val));
          ensures this.val == \old(this.val) + 1;
          assignable this.val;
          assignable<permissions> \strictly_nothing;
      @*/
    private /*@ helper @*/ void write() {
        this.val++;
    }

    /*@ public normal_behavior
          requires \dl_readPermission(\permission(this.val));
          ensures \result == this.val;
          assignable \strictly_nothing;
          assignable<permissions> \strictly_nothing;
      @*/
    private /*@ helper @*/ int read() {
        return this.val;
    }

    /*@ public normal_behavior
          requires \dl_currentThread() != this;
          requires !\dl_readPermission(\permission(this.rds));
          ensures !\dl_readPermission(\permission(this.rds));
          assignable<permissions> this.rds, this.lockedRds, this.val;
          assignable<heap> this.val, this.rds, this.lockedRds;
          diverges true; @*/
    public /*@ helper @*/ void doWrite() {
        boolean done = false;
        /*@ loop_invariant !\dl_readPermission(\permission(this.rds));
            assignable<permissions> this.rds, this.lockedRds, this.val;
            assignable<heap> this.lockedRds, this.rds, this.val; @*/
        while(!done) {
            lock();
            if(rds == 0) {
              write();
              done = true;
            }
            unlock();
        }
    }

    /*@ public normal_behavior
          requires \dl_currentThread() != this;
          requires !\dl_readPermission(\permission(this.rds));
          ensures !\dl_readPermission(\permission(this.rds));
          assignable<permissions> this.rds, this.val, this.lockedRds;
          assignable<heap> this.rds, this.val, this.lockedRds; @*/
    public /*@ helper @*/ int doRead() {
        lock(); rds++; unlock(); // read lock
        int r = read();
        lock(); rds--; unlock(); // read unlock
        return r;
    }

    /*@ public normal_behavior
          requires \dl_currentThread() != this;
          requires !\dl_readPermission(\permission(this.rds));
          ensures \old(\dl_readPermission(\permission(this.val))) ==> rds > 0;
          ensures \dl_writePermissionObject(this, \old(\permission(this.rds)));
          ensures \dl_writePermissionObject(this, \old(\permission(this.lockedRds)));
          ensures rds >= 0;
          ensures rds == 0 ==>
            \dl_writePermissionObject(this, \old(\permission(this.val)));
          ensures \dl_readPermissionObject(this, \old(\permission(this.val)));
          ensures \permission(this.rds) ==
            \dl_transferPermission(\dl_FALSE(), this, \dl_currentThread(), 0,
              \old(\permission(this.rds)));
          ensures \permission(this.lockedRds) ==
            \dl_transferPermission(\dl_FALSE(), this, \dl_currentThread(), 0,
              \old(\permission(this.lockedRds)));
          ensures \permission(this.val) ==
            \dl_transferPermission(\dl_FALSE(), this, \dl_currentThread(), 0,
              \old(\permission(this.val)));
          ensures this.lockedRds == this.rds;
          assignable<permissions> this.rds, this.lockedRds, this.val;
          assignable<heap> this.lockedRds; @*/
    public native void lock();

    /*@ public normal_behavior
          requires \dl_currentThread() != this;
          requires \dl_writePermission(\permission(this.rds));
          requires \dl_writePermission(\permission(this.lockedRds));
          requires rds >= 0;
          ensures \permission(this.rds) == \dl_returnPermission(\dl_currentThread(), this,
            \old(\permission(this.rds)));
          ensures \permission(this.lockedRds) == \dl_returnPermission(\dl_currentThread(), this,
            \old(\permission(this.lockedRds)));
          ensures \old(this.rds) <= \old(this.lockedRds) ==>
            \permission(this.val) == \dl_returnPermission(\dl_currentThread(), this,
              \old(\permission(this.val)));
          ensures \old(this.rds) > \old(this.lockedRds) ==>
            \permission(this.val) == \dl_transferPermission(\dl_TRUE(), this, \dl_currentThread(), 0,
              \dl_returnPermission(\dl_currentThread(), this, \old(\permission(this.val))));
          assignable<permissions> this.rds, this.lockedRds, this.val;
          assignable<heap> this.rds, this.lockedRds, this.val; @*/
    public native void unlock();

    private int rds;
    //@ private instance ghost int lockedRds;

}
