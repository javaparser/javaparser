
//@ pure immutable nullable_by_default
abstract class testtype implements IJmlPrimitiveType {
    
    //@ axiom (\forall testtype t; t != null; t.suc().prev() == t);
    
    static /*@ non_null */ public testtype zero;
    
    //@ skipesc
    private testtype() {}
    
    //@ ensures \result == zero;
    //@ helper function
    static public testtype testtype() {
        return zero;
    }
    
    //@ public normal_behavior
    //@ helper function
    abstract public testtype suc();
    
    //@ public normal_behavior
    //@ helper function
    abstract public testtype prev();
    
    //@ public normal_behavior
    //@ ensures this.suc().prev() == this;
    public abstract void lemma();
}

public class Test {
    
    //@ public normal_behavior
    public void lemma1(testtype t) {
        //@ ghost testtype tt = t;
        //@ assert tt.suc() == t.suc();
    }
    
    //@ public normal_behavior
    //@ ensures t.suc().prev() == t;
    public void lemma2(testtype t) { t.lemma(); }
    
    //@ public normal_behavior
    //@ ensures t.suc().prev() == t;
    //@ skipesc // FIXME - this form of the lemma needs better triggering perhaps?
    public void lemma2a(testtype t) { }
    
    //@ public normal_behavior
    //@ ensures testtype.testtype() == testtype.zero;
    public void lemma3(testtype t) {}
    
    public void m() {
        //@ ghost testtype t2 = testtype.zero.suc().suc().prev().suc();
        testtype.zero.suc().lemma();
        //@ assert t2.prev() == testtype.zero.suc();
    }
}
