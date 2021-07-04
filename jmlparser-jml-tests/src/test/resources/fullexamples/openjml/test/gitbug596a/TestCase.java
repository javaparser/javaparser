public class TestCase {
    public int a = 1;

    //@ requires b >= +a;
    public void plus(int b) {}
}