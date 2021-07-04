public class Parent {

  /*@ non_null */ public Object o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Object oo) {
     o = oo;
  }
}

