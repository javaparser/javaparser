public class Unreachable {
    public void assertFalse() {
        if (true) {
            // hi!
        } else {
            //@ assert false;
        }
    }

    public void unreachable() {
        if (true) {
            // hi!
        } else {
            //@ unreachable;
        }
    }
}