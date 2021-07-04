public class ZeroInit {
    //@ public normal_behavior
    //@   requires size > 0;
    //@   ensures \result != null;
    //@   ensures \result.length == size;
    //@   ensures \result[0] == 0;
    public static int[] allZeroes(int size) {
        int[] arr = new int[size];
        return arr;
    }
}