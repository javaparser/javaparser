// Outer environment is nullable by default

//@ non_null_by_default
public class Test {
    
    
    //@ public normal_behavior
    //@   ensures \fresh(\result);
    public static TestB m(TestA t) {
        //@ assert t != null;
        TestA tt = new TestA() {
            //@ public invariant t != null;
            public TestA show(TestA aa) {
                int k = t.f;  // should not have a null-dereference error
                k = aa.f; // should not have null dereference error either
                return t;  // t should be non-null because the argument of m() is // EXPECTED ERROR
            }
        };
        return TestB.wrap(tt);
    }
}

//@ non_null_by_default
class TestB {
    
    //@ public normal_behavior
    //@   ensures true;
    //@ pure
    public TestB(TestA a) {}
    
    //@ public normal_behavior
    //@   ensures \fresh(\result);
    public static TestB wrap(TestA a) { return new TestB(a); }
}

//@ non_null_by_default
class TestA {
 
    public int f = 10;

    //@ ensures \result == null;
    public /*@ nullable */ TestA show(TestA aa) {
        return null;
    }
}