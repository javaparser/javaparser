
public class NoModelTest {
  public boolean equals(final Object the_other) {
    return true;
  }
  
  public int hashCode() {
    return 0;
  }
  
  public static void main(String... args) {
      NoModelTest t = new NoModelTest();
      int i = t.hashCode();
      boolean b = t.equals(t);
      System.out.println("RESULT: " + i + " " + b);
  }
}
