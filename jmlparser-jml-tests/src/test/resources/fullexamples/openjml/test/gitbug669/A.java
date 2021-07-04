public final class A {
  //@ requires a >= 0 && a <= 10;
  //@ ensures \result == a + 1;
  //@ pure
  public int add(int a) {
    return a + 1;
  }
  
  public static void main(String[] args) {
    System.out.println(new A().add(10));
  }
}

// This bug showed a (distinct NULL) SMT assertion because there are no function objects.
// It does not show up in the expected output -- one has to turn on -show to see the difference,
// but that is not very testable.

