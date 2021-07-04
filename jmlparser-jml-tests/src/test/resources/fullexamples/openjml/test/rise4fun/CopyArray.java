public class CopyArray {
    //@ requires a.length == b.length;
    //@ requires 0 <= iBegin && iBegin < a.length && 0 <= iEnd && iEnd < a.length && iBegin <= iEnd;
    //@ ensures (\forall int i; iBegin <= i && i < iEnd; a[i] == b[i]);
    public static void CopyArray(int[] b, int iBegin, int iEnd, int[] a) {
        int k = iBegin;
        ;
        //@ maintaining iBegin <= k && k <= iEnd;
        //@ maintaining (\forall int i; iBegin <= i && i < k; a[i] == b[i]);
        //@ decreases iEnd  - k;
        while (iEnd - k > 0) {
            a[k] = b[k];
            k = k + 1;
        }
    }
}
