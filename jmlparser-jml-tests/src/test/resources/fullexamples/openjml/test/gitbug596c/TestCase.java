public class TestCase {
    public int a = 1;

    //@ requires b >= Math.max(0, (int)(-1.0 * a));
    public void timesMinusOneFloat(int b) {}
}