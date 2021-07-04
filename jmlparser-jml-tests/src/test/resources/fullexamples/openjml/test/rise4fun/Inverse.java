// It specifies and verifies that the array a is an inverse of the array b
public class Inverse {
    //@ requires true;
    //@ ensures \result == false ==> ((x.length != y.length) || (\exists int i; 0 <= i && i < x.length; x[i] != y[x.length - 1 -i]));
    //@ ensures \result == true ==> x.length == y.length && (\forall int i; 0 <= i && i < x.length; x[i] == y[x.length - 1 - i]);
    public static boolean Inverse(int[] x, int[] y) {
        if (x.length != y.length) return false;
        assert x.length == y.length;
        int index = 0;
        //@ maintaining 0 <= index && index <= x.length && x.length == y.length;
        //@ maintaining (\forall int i; 0 <= i && i < index; x[i] == y[x.length -1 - i]);
        //@ decreases x.length - index;
        while (index < x.length) {
            if (x[index] != y[x.length - 1 - index]) {
                return false;
            } else {
                index = index + 1;
            }
        }
        return true;
    }
}