public class TestCase {
    public int a = 1;

    //@ requires b >= Math.max(0, -a);
    public void minus(int b) {}
}
