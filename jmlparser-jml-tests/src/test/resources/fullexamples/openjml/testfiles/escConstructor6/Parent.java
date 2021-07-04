public class Parent {

  /*@ non_null */ public Integer o;

  //@ ensures o.equals(oo);
  //@ pure
  public Parent(/*@ non_null*/ Integer oo) {
     o = oo;
  }
}

