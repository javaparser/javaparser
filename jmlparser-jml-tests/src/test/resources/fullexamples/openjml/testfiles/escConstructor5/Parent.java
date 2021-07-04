public class Parent {

  /*@ non_null */ public String o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ String oo) {
     o = oo;
  }
}

