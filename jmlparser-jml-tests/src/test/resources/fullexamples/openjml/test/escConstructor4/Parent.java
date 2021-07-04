public class Parent {

  /*@ nullable */ public Object o;

  //@ ensures oo.equals(o);
  //@ pure
  public Parent(/*@ non_null*/ Object oo) {
     o = oo;
  }
}

