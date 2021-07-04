public class AddLoop {
    //@ requires Integer.MIN_VALUE <= x + y <= Integer.MAX_VALUE;
    //@ requires Integer.MIN_VALUE < y;
    //@ ensures \result == x + y;
    public static int AddLoop(int x, int y) {
        int sum = x;
        if (y > 0) {
            int n = y;

            //@ maintaining sum == x + y - n && 0 <= n;
            //@ decreases n;
            while (n > 0) {
                sum = sum + 1;
                n = n - 1;
            }
        } else {
            int n = -y;

            //@ maintaining sum == x + y + n && 0 <= n;
            //@ decreases n;
            while (n > 0) {
                sum = sum - 1;

                n = n - 1;
            }
        }
        return sum;

    }
}