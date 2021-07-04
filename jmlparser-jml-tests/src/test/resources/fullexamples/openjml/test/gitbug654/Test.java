//@ nullable_by_default
class C<T> {
}
//@ nullable_by_default
class B {
    //@ nullable
    public C<Integer> xyz;

    //@ public normal_behavior
    //@   ensures true;
    public B() {
    }

    //@ public normal_behavior
    //@   ensures true; //\result == xyz;
    public C<Integer> getXyz() {
        return xyz;
    }
}
//@ nullable_by_default
public final class Test {
    
    //@ public normal_behavior
    //@   ensures true;
    //@ pure
    public Test(B b) {  // fails feasibility check #1 (end of preconditions)
        if (false) {
            b.getXyz();
        }
    }

    //@ public normal_behavior
    //@   ensures true;
    public void TestMethod(B b) {  // fails feasibility check #1 (end of preconditions)
        if (false) {
            b.getXyz();
        }
    }
}