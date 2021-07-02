public class Transfer {
  int a; 
  
  /*@ public normal_behavior
         requires \dl_currentThread() == this;
         requires \permission(this.a) == \dl_initFullPermission();
	 ensures this.a == 10;
         ensures \dl_writePermission(\permission(this.a));
	 assignable this.a;
         assignable<permissions> this.a;
    @*/
  void /*@ helper @*/ entry() {
     Thread1 t1 = new Thread1(this);
     Thread2 t2 = new Thread2(this, t1);
     t1.start();
     t2.start();
     // this.a = 10;
     t1.join();
     // this.a = 10;
     t2.join();
     this.a = 10;
  }
}

class Thread1 {
  Transfer t;

  public Thread1(Transfer tr) {
    this.t = tr;
  }

  /*@ public normal_behavior
        requires this != \dl_currentThread();
        requires \dl_readPermission(\permission(t.a));
        ensures \permission(t.a) == \dl_transferPermission(\dl_TRUE(),
          \dl_currentThread(), this, 0, \old(\permission(t.a)));
        assignable \strictly_nothing; assignable<permissions> t.a; @*/
  /*@ helper @*/ public native void start();

  /*@ public normal_behavior
        requires this != \dl_currentThread();
        ensures \permission(t.a) == \dl_returnPermission(this,
          \dl_currentThread(), \old(\permission(t.a)));
        assignable \strictly_nothing; assignable<permissions> t.a;
    @*/
  /*@ helper @*/ public native void join();

}

class Thread2 {
  Transfer t; Thread1 t1;

  public Thread2(Transfer tr, Thread1 t1) {
    this.t = tr; this.t1 = t1;
  }

  /*@ public normal_behavior
        requires this != \dl_currentThread();
        requires \dl_readPermission(\permission(t.a));
        ensures \permission(t.a) == \dl_transferPermission(\dl_TRUE(),
          \dl_currentThread(), this, 1, \old(\permission(t.a)));
        assignable \strictly_nothing; assignable<permissions> t.a; @*/
  /*@ helper @*/ public native void start();

  /*@ public normal_behavior
        requires this != \dl_currentThread();
        ensures \permission(t.a) == \dl_returnPermission(this, \dl_currentThread(), 
          \dl_returnPermission(this.t1, this, \old(\permission(t.a))));
        assignable \strictly_nothing; assignable<permissions> t.a; @*/
  /*@ helper @*/ public native void join();
}
