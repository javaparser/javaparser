// This version of issue #650 has the axiom in the class and first
interface A {
    /*@ immutable pure public static model class Content {
      @     axiom (\forall Content c; (\forall Object o; c.P(o)));
      @     public normal_behavior
      @       ensures true;
      @     function
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