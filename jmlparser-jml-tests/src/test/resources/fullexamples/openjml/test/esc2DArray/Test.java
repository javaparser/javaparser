public class Test {
    
    //@ requires m >= 0 && n>= 0;  // FIXME - fails to prove if m is allowed to be 0
    //@ ensures \fresh(\result);
    //@ ensures \result.length == m;
    //@ ensures \forall int i; 0<=i<m; \result[i] != null && \result[i].length == n;
    //@ ensures \forall int e; 0<=e<m; \forall int k; 0 <= k < n; \result[e][k] == e+k;
    public static int[][] m(int m, int n) {
        //@ assume m == 2 && n == 2;
        int[][] a = new int[m][n];
        //@ assert a != null;
        //@ assert a.length == m;
        //@ assert m > 0 ==> a[0] != null;  // FIXME - proof fails if the following are not assumed
        //@ assert m > 0 ==> a[0].length == n;
        //@ assert \forall int i; 0 <= i < m; a[i] != null && a[i].length == n;
        //@ assert \forall int e; 0<=e<m; \forall int k; 0 <= k < m; (e != k ==> a[e] != a[k]);
        x: ;
        
        //@ loop_invariant 0 <= i <= m;
        //@ loop_invariant \forall int k; 0<=k<m; a[k] != null && a[k].length == n;
        //@ loop_invariant \forall int e; 0<=e<m; \forall int k; 0 <= k < m; (e != k ==> a[e] != a[k]);
        //@ loop_invariant \forall int e; 0<=e<i; \forall int k; 0 <= k < n; a[e][k] == e+k;
        //@ loop_modifies a[*][*];
        //@ loop_decreases m-i;
        for (int i=0; i<m; i++) {
            //@ loop_invariant 0 <= j <= n;
            //@ loop_invariant \forall int k; 0<=k<m; a[k] != null && a[k].length == n;
            //@ loop_invariant \forall int e; 0<=e<m; \forall int k; 0 <= k < m; (e != k ==> a[e] != a[k]);
            //@ loop_invariant \forall int e; 0<=e<i; \forall int k; 0 <= k < n; a[e][k] == e+k;
            //@ loop_invariant \forall int k; 0 <= k < j; a[i][k] == i+k;
            //@ loop_modifies a[*][*];
            //@ loop_decreases n-j;
            for (int j=0; j<n; j++) {
                a[i][j] = i+j;
            }
            //@ assert \forall int k; 0 <= k < n; a[i][k] == i+k;
        }
        //@ assert \forall int e; 0<=e<m; \forall int k; 0 <= k < n; a[e][k] == e+k;
        return a;
    }
    
    public static void mm1(int[][] a) {
        //@ assume a != null;
        //@ assume a.length == 5;
        //@ assume a[1] != null && a[2] != null;
        //@ assume a[1].length == 6;
        //@ assume a[2].length == 7;
        //@ assume a[2][3] ==7;
        a[1][2] = 13;
        //@ assert a.length == 5; //OK
        //@ assert a[1].length == 6; //OK
        //@ assert a[2].length == 7; //OK
        //@ assert a[2][3] ==7; //OK
    }
    
    public static void mm2(int[][] a) {
        //@ assume a != null;
        //@ assume a.length == 5;
        //@ assume a[1] != null && a[2] != null;
        //@ assume a[1].length == 6;
        //@ assume a[2].length == 7;
        //@ assume a[2][3] ==7;
        //@ havoc a[*][*];
        //@ assert a.length == 5 && a[1].length == 6 && a[2].length == 7 && a[2][3] ==7;  // FAILS
        // @ assert a.length == 5;  // FAILS
        // @ assert a[1].length == 6;  // FAILS
        // @ assert a[2].length == 7;  // FAILS
        // @ assert a[2][3] ==7;  // FAILS
    }
    
    public static void mm3(int[][] a) {
        //@ assume a != null;
        //@ assume a.length == 5;
        //@ assume a[1] != null && a[2] != null;
        int[] b = a[1];
        //@ assume a[1].length == 6;
        //@ assume a[2].length == 7;
        //@ assume a[2][3] ==7;
        a[1][2] = 13;
        //@ assert a.length == 5; // OK
        //@ assert a[1].length == 6; // OK
        //@ assert a[2].length == 7; // OK
        //@ assert a[2][3] ==7; // OK
        //@ assert b[2] == 13; // OK
    }
}