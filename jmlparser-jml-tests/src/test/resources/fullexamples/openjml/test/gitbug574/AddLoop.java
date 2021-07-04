public class AddLoop {
    //@ requires -1000000 < x & x < 1000000 & -1000000 < y & y < 1000000;
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
