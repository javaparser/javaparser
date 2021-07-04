// This version has the axiom not in the class, but first
interface A {
    //@ axiom (\forall Content c; (\forall Object o; c.P(o)));

    /*@ immutable pure public static model class Content {
      @     public normal_behavior
      @       ensures true;
      @     function helper
      @     public boolean P(nullable Object key);

      @ }
      @
      @*/
    
    //@ public model instance non_null Content content;

    //@ public invariant content.P(null);
}
public final class B {
    public B(/*@ non_null */ A a) {
        this.a = a;
    }
    
    //@ non_null
    public A a;
        
    //@ public normal_behavior
    //@   ensures true;
    public void testMethod() {
    }
}