public interface LockSpec {

  /*@ model_behavior
      accessible<heap> fpLock();
      accessible<permissions> fpPerm();
      model boolean lockState(boolean locked); @*/

  /*@ model_behavior
      accessible<heap> fpLock();
      accessible<permissions> \nothing;
      model Lock lockRef(); @*/

  /*@ model_behavior
      accessible<heap> \nothing;
      accessible<permissions> fpPerm();
      model boolean lockStatus(boolean locked); @*/

  /*@ model_behavior
      accessible<heap> fp();
      accessible<permissions> \nothing;
      model \locset fp(); @*/

  /*@ model_behavior
      accessible<heap> fpLock();
      accessible<permissions> \nothing;
      model \locset fpLock(); @*/

  /*@ model_behavior
      accessible<heap> \nothing;
      accessible<permissions> fpPerm();
      model \locset fpPerm(); @*/

  /*@ model_behavior
      accessible<heapAtPre> \nothing;
      accessible<heap> fpLock();
      accessible<permissionsAtPre> fpPerm();
      accessible<permissions> fpPerm();
      model two_state boolean lockTransfer(); @*/

  /*@ model_behavior
      accessible<heapAtPre> \nothing;
      accessible<heap> fpLock();
      accessible<permissionsAtPre> fpPerm();
      accessible<permissions> fpPerm();
      model two_state boolean unlockTransfer(); @*/

  /*@ model_behavior
      requires \old(lockRef()) == lockRef();
      requires \old(this.\inv);
      requires lockRef() != \dl_currentThread();
      ensures \result;
      model two_state boolean lockConsistent() { return 
        (((\old(lockState(\dl_FALSE())) && \old(lockStatus(\dl_FALSE())) && lockTransfer()) ==> (lockState(\dl_TRUE()) && lockStatus(\dl_TRUE())))
         &&
         ((\old(lockState(\dl_TRUE())) && \old(lockStatus(\dl_TRUE())) && unlockTransfer()) ==> (lockState(\dl_FALSE()) && lockStatus(\dl_FALSE())))
        );
      } @*/
}

public interface Lock {
  //@ public instance ghost LockSpec spec;

  /*@ normal_behavior
      requires spec.lockStatus(\dl_FALSE());
      ensures spec.lockStatus(\dl_TRUE());
      ensures spec.lockTransfer();
      assignable<heap> \strictly_nothing;
      assignable<permissions> spec.fpPerm(); @*/
  public /*@ helper @*/ native void lock();

  /*@ normal_behavior
      requires spec.lockStatus(\dl_TRUE());
      ensures spec.lockStatus(\dl_FALSE());
      ensures spec.unlockTransfer();
      assignable<heap> spec.fp(); // should be done by the prover
      assignable<permissions> spec.fpPerm(); @*/
  public /*@ helper @*/ native void unlock();
}

public class Counter implements LockSpec {
   private int val;
   private /*@ non_null @*/ Lock lock;
   //@ invariant this.lock != \dl_currentThread() && this.lock.spec == this && \dl_writePermission(\permission(this.lock)) && \dl_writePermission(\permission(this.lock.spec));
   //@ accessible<heap> \inv : this.lock, lock.spec;
   //@ accessible<permissions> \inv : this.lock, lock.spec;

   /*@ model boolean lockState(boolean locked) {
          return (\permission(this.val) == (locked ? \dl_slice1(\dl_owner2(\dl_currentThread(), lockRef())) : \dl_slice1(\dl_owner1(lockRef())))) ;
        } @*/
   /*@ model \locset fp() { return \singleton(this.val); } @*/
   /*@ model \locset fpPerm() { return \singleton(this.val); } @*/
   /*@ model \locset fpLock() { return \singleton(this.lock); } @*/
   /*@ model two_state boolean lockTransfer() { return (\permission(this.val) == \dl_transferPermission(\dl_FALSE(), lockRef(), \dl_currentThread(), 0, \old(\permission(this.val)))); } @*/
   /*@ model two_state boolean unlockTransfer() { return (\permission(this.val) == \dl_returnPermission(\dl_currentThread(), lockRef(), \old(\permission(this.val)))); } @*/

   /*@ model Lock lockRef() { return this.lock; } @*/
   /*@ model boolean lockStatus(boolean locked) { return (locked ? \dl_writePermission(\permission(this.val)) : !\dl_readPermission(\permission(this.val))); } @*/

   /*@ normal_behavior
        requires lockStatus(\dl_FALSE());
        ensures lockStatus(\dl_FALSE());
        assignable<heap> fp();
        assignable<permissions> fpPerm(); @*/
   public void increase() {
      lock.lock();
      val++;
      lock.unlock();
   }
}


