//@ non_null_by_default
class A {
    //@ spec_public
    private String ssss;
    
    public String pppp;
    
    //@ private normal_behavior
    //@   requires true;
    //@ pure
    public A() {
        ssss = "hello";
        pppp = "hello";
    }
}
//@ non_null_by_default
public class B {
    //@ non_null
    B b;
    
    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public B(A aaaa) {
        //@ assert aaaa.pppp != null;  // OpenJML is OK
        //@ assert aaaa.ssss != null;  // OpenJML reports error
        b = this;
    }
    
    
    public B(B bbbb) {
        //@ assert bbbb.b != null; // should be true
        //@ assert bbbb != this;
        b = this;
    }
    
    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public void testMethod(A aaaa) {
        //@ assert aaaa.ssss != null;  // fine
    }
    
}

class C  {
    //@ non_null
    public C cccc;
        
    //@ public normal_behavior
    //@   requires true;
    //@ pure
    public C() {
        init(this);
        //@ assert cccc != null;
    }
    
    //@ public normal_behavior
    //@ assignable cccc;
    //@ ensures this.cccc == c.cccc;
    public void init(C c) {
        //@ assert c.cccc != null; // Not true when called in a constructor with c == this
        cccc = c.cccc;
        //@ assert this.cccc != null;
    }
}