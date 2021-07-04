public class TestCase {
    public int a = 1;

    //@ requires b >= Math.max(0, -1 * a);
    public void timesMinusOne(int b) {}
}