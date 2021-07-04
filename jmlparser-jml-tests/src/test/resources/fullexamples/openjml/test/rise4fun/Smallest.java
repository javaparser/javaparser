public class Smallest {
    //@ requires true;
    //@ ensures \result == -1 ==> a.length == 0;
    //@ ensures \result > -1 ==> (\forall int i; 0 <= i && i < a.length; a[\result] <= a[i]);
    static public int Smallest(int[] a) {
        if (a.length == 0) return -1;

        int index = 0;
        int smallest = 0;
        //@ maintaining 0 <= index && index <= a.length;
        //@ maintaining 0 <= smallest && smallest < a.length;
        //@ maintaining (\forall int i; 0 <= i && i < index; a[smallest] <= a[i]);
        //@ decreases a.length - index;
        while (a.length - index > 0) {
            if (a[index] < a[smallest]) {
                smallest = index;
            }
            index = index + 1;
        }
        return smallest;
    }
}
