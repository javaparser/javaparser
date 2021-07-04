public class BinarySearch {
    //@ requires (\forall int i, j; 0 <= i && i < j && j < arr.length; arr[i] <= arr[j]);
    //@ ensures \result == -1 ==> (\forall int i; 0 <= i && i < arr.length; arr[i] != key);
    //@ ensures 0 <= \result && \result < arr.length ==> arr[\result] == key;
    public static int BinarySearch(int[] arr, int key) {
        if (arr.length == 0) {
            return -1;
        } else {
            int low = 0;
            int high = arr.length;
            int mid = low + (high - low) / 2;
            //@ maintaining 0 <= low && low <= high  && high <= arr.length && mid == low + (high - low) / 2;
            //@ maintaining (\forall int i; 0 <= i && i < low; arr[i] < key);
            //@ maintaining (\forall int i; high <= i && i < arr.length ==> key < arr[i]);
            //@ decreases high - low;
            while (low < high && arr[mid] != key) {
                if (arr[mid] < key) {
                    low = mid + 1;
                } else {
                    high = mid;
                }
                mid = low + (high - low) / 2;
            }
            if (low >= high) {
                return -1;
            }
            return mid;
        }


    }
}