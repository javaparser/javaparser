public class MBBug {

    public MBBug() {
    }

    //@ requires n >= 0;
    //@ measured_by n;
    //@ ensures \result == 0;
    public int zero (int n) {
        if (n == 0) { return 0; }
        return zero(n);
    }
}

// This submission wanted to check measured_by, which is not supported
// yet
