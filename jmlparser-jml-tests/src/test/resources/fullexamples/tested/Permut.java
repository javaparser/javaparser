// FROM JJBMC -- https://github.com/JonasKlamroth/JJBMC/blob/master/src/VerifyThis2021/Permut.java
package VerifyThis2021;

public class Permut {
    static public int max;

    /*@ requires A != null;
      @ requires (\forall int i; 0 <= i < A.length; A[i] == oldA[i]);
      @ //requires (\forall int m; 0 <= m < A.length; A[m] <= max);
      @ //ensures (\forall int m; 0 <= m < A.length; A[m] <= max);
      @ ensures !\result ==> (\forall int i; 0 <= i < A.length; A[i] == \old(A[i]));
      @ ensures !\result ==> (\forall int j; 0 <= j < A.length - 1; A[j] >= A[j + 1]);
      @ ensures \result ==> (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < A.length; \old(A[i]) == A[j]));
      @ ensures \result ==> !(\exists int i; 0 <= i < A.length; (\forall int j; 0 <= j < A.length; A[i] != \old(A[j])));
      @ ensures \result ==> (\exists int j; 0 <= j < A.length; (\forall int k; 0 <= k < j; A[k] == \old(A[k])) && \result == A[j] > \old(A[j]));
      @ assignable A[*];
     */
    public static boolean next2(int[] A, int[] oldA) {
        int i = A.length - 1;
        while (i > 0 && A[i - 1] >= A[i]) {
            i = i - 1;
        }

        if (i <= 0) return false;

        int j = A.length - 1;
        while (A[j] <= A[i - 1]) {
            j = j - 1;
        }

        int temp = A[i - 1];
        A[i - 1] = A[j];
        A[j] = temp;

        j = A.length - 1;
        while (i < j) {
            temp = A[i];
            A[i] = A[j];
            A[j] = temp;
            i = i + 1;
            j = j - 1;
        }

        return true;
    }


    /*@ requires A != null && A.length <= 5;
      @ ensures !\result ==> (\forall int i; 0 <= i < A.length; A[i] == \old(A[i]));
      @ ensures !\result ==> (\forall int j; 0 <= j < A.length - 1; A[j] >= A[j + 1]);
      @ ensures \result ==> (\forall int i; 0 <= i < A.length; (\exists int j; 0 <= j < A.length; \old(A[i]) == A[j]));
      @ ensures \result ==> !(\exists int i; 0 <= i < A.length; (\forall int j; 0 <= j < A.length; A[i] != \old(A[j])));
      @ ensures \result ==> (\exists int j; 0 <= j < A.length; (\forall int k; 0 <= k < j; A[k] == \old(A[k])) && \result == A[j] > \old(A[j]));
      @ assignable A[*];
     */
    public static boolean next(int[] A) {
        int i = A.length - 1;
        while (i > 0 && A[i - 1] >= A[i]) {
            i = i - 1;
        }

        if (i <= 0) return false;

        int j = A.length - 1;
        while (A[j] <= A[i - 1]) {
            j = j - 1;
        }

        int temp = A[i - 1];
        A[i - 1] = A[j];
        A[j] = temp;

        j = A.length - 1;
        while (i < j) {
            temp = A[i];
            A[i] = A[j];
            A[j] = temp;
            i = i + 1;
            j = j - 1;
        }

        return true;
    }

    /*@ requires A != null && B != null && A.length == B.length;
      @ requires (\exists int i; 0 <= i < A.length; A[i] != B[i]);
      @ ensures (\exists int j; 0 <= j < A.length; (\forall int k; 0 <= k < j; A[k] == B[k]) && \result == A[j] < B[j]);
     */
    public static /*@ pure */ boolean comesFirst(int[] A, int[] B) {
        int idx = 0;
        /*@
          @ loop_invariant (\forall int i; 0 <= i < idx; A[i] == B[i]);
          @ loop_invariant idx >= 0 && idx < A.length;
          @ decreases A.length - idx;
          @ assignable \nothing;
         */
        while (A[idx] == B[idx]) {
            idx++;
        }

        return A[idx] < B[idx];
    }

    public static /*@ pure */ int fac(int num) {
        int result = 1;
        for (int i = num; i > 0; ++i) {
            result += i;
        }
        return result;
    }

    public static int inc(int i) {
        return i + 1;
    }

    /*@ requires A != null && A.length > 0 && size < 5;
      @ requires (\forall int i; 0 <= i < A.length; A[i] == i);
      @ ensures false;
     */
    public static int permut(int[] A, int size) {
        if (A == null) return 0;


        int idx = 1;

        int[] B = new int[A.length];
        for (int i = 0; i < A.length; ++i) {
            B[i] = A[i];
        }
        while (idx < size && next2(A, B)) {
            idx++;
            assert comesFirst(B, A);
            B = A;
            A = new int[B.length];
            for (int i = 0; i < A.length; ++i) {
                A[i] = B[i];
            }
        }
        return idx;
    }

    /*@ requires a != null;
      @ ensures (\forall int i; 0 <= i < a.length - 1; a[i] <= a[i + 1]);
      @ ensures (\forall int i; 0 <= i < a.length; (\exists int j; 0 <= j < a.length; \old(a[i]) == a[j]));
      @ ensures !(\exists int i; 0 <= i < a.length; (\forall int j; 0 <= j < a.length; a[i] != \old(a[j])));
      @ assignable a[*];
     */
    public static void sort(int[] a) {
    }
}
