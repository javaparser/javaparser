/** class to demonstrate the need for \num_of in JML. */
public class Count{
    /** returns the number of elements in arr[low..k-1] equal to e. */
    /*@
        requires 0 <= low <= k <= high <= arr.length;
        ensures k <= low ==> \result == 0;
        ensures low < k <= high
                ==> \result == counteq(arr, e, low, high, k-1)
                               + (e == arr[k-1] ? 1 : 0);
        ensures 0 <= \result <= k-low;
    @*/
    /*@ pure @*/ 
    int counteq(int arr[], int e, int low, int high, int k) {
        if (k <= low) {
            return 0;
        } else {
            return counteq(arr, e, low, high, k-1)
                   + (e == arr[k-1] ? 1 : 0);
        }
    }


    /*@
        requires 0 <= low <= high <= arr.length;
        ensures \result == counteq(arr, e, low, high, high);
        ensures 0 <= \result <= high-low;
    @*/
    /*@ pure @*/ 
    int count(int arr[], int e, int low, int high) {
        int sum = 0;
        //@ maintaining low <= i <= high;
        //@ maintaining sum == counteq(arr, e, low, high, i);
        for (int i = low; i < high; i++) {
            if (arr[i] == e) {
                sum++;
            }
        }
        return sum;
    }
}
