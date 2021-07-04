public class IntSetClient {
    //@ requires is.size() > 0;
    public static void test(IntSet is) {
        int k = is.choose();
        //@ assert is.contains(k);
    }
}
