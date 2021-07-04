public class Container {
    public static /*@ non_null @*/ Object c = new Object();

    /*@ public normal_behavior
      @   assignable c;
      @*/
    public static void allocate() {
        c = new Object();
    }

    public static void test() {
        allocate();
        //@ assert c instanceof Object;
    }
}

// Note: the allocate call has no postconditions, which normally would mean that c could be anything
// after the call. However c is delcared non_null and has type Object, so the assertion should be provable.
