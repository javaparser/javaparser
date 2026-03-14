class TokenTest {
    //@ invariant test : x == x;

    /*@ private normal_behavior
      @   ensures key == null ==> \result == NULL_KEY;
      @   ensures key != null ==> \result == key;
      @*/
    public void foo() {
    }
}