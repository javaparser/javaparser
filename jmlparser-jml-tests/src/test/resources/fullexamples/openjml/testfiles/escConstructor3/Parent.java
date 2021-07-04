public class Parent {

  /*@ nullable */ public Object o;

  //@ ensures o != null && o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Object oo) {
     o = oo;
  }
}

