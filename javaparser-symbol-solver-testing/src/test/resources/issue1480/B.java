
public class B extends A {

//  public void test1() {
//    foo(); // should be inherited from A, so there should exist an (implicit) method org.testapp.B.foo()
//  }

  public void test2() {
    bar(); // should not be resolvable, since bar() is private in A and not inherited by B
  }
}
