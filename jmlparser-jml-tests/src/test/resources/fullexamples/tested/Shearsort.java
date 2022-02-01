// FROM JJBMC https://github.com/JonasKlamroth/JJBMC/blob/master/src/VerifyThis2021/Shearsort.java

package VerifyThis2021;

public class Shearsort {
    // Sorts M in snake-like order, assuming that M is an n × n matrix.
    /*@ requires M != null && M.length == n && M.length == 2;
      @ requires (\forall int i; 0 <= i < M.length; M[i] != null);
      @ requires (\forall int i; 0 <= i < M.length; M[i].length == n);
      @ requires (\forall int i; 0 <= i < M.length; (\forall int k; 0 <= k < M.length; (\exists int j; 0 <= j < M.length; M[i][k] == j)));
      @ ensures (\forall int i; 0 <= i < M.length; i % 2 == 0 ==>
      @     (\forall int j; 0 <= j < M[i].length - 1; M[i][j] <= M[i][j + 1]));
      @ //ensures (\forall int i; 0 <= i < M.length; i % 2 != 0 ==>
      @  //   (\forall int j; 0 <= j < M[i].length - 1; M[i][j] >= M[i][j + 1]));
      @ assignable \everything;
     */
    void shearsort(int n, int[][] M) {
        int log = n;
        for (int i = 0; i < log + 1; i++) {
            for(int tid = 0; tid < n; tid++) {
                sortrow(M, tid, tid % 2 == 0);
            }
            for(int tid = 0; tid < n; tid++) {
                sortcolumn(M, tid);
            }
        }
    }

    // An alternative version of shearsort, that only uses sort-row.
    void alternativeshearsort(int n, int[][] M){
        int log = 0;
        for(int i = 0; i < log; ++i) {
            for(int tid = 0; tid <= n; tid++) {
                sortrow(M, tid, tid % 2 == 0);
            }
            transpose(M);
            for(int tid = 0; i <=n; tid++) {
                sortrow(M, tid, true);
            }
            transpose(M);
        }
    }

    /*@ requires m != null;
      @ requires (\forall int i; 0 <= i < m.length; m[i] != null);
      @ requires (\forall int i; 0 <= i < m.length; m[i].length == m.length);
      @ requires tid >= 0 && tid < m.length;
      @ ensures (\forall int i; 0 <= i < m[tid].length - 1; m[i][tid] <= m[i + 1][tid]);
      @ ensures (\forall int i; 0 <= i < m.length;
      @     (\exists int j; 0 <= j < m[i].length;
      @         \old(m[i][tid]) == m[j][tid]));
      @ assignable m[*][tid];
     */
    private void sortcolumn(int[][] m, int tid) {

    }

    /*@ requires m != null;
      @ requires (\forall int i; 0 <= i < m.length; m[i] != null);
      @ requires (\forall int i; 0 <= i < m.length; m[i].length == m.length);
      @ requires tid >= 0 && tid < m.length;
      @ ensures ascending ==> (\forall int i; 0 <= i < m[tid].length - 1; m[tid][i] <= m[tid][i + 1]);
      @ ensures !ascending ==> (\forall int i; 0 <= i < m[tid].length - 1; m[tid][i] >= m[tid][i + 1]);
      @ ensures (\forall int i; 0 <= i < m.length;
      @     (\exists int j; 0 <= j < m[i].length;
      @         \old(m[tid][i]) == m[tid][j]));
      @ assignable m[tid][*];
     */
    private void sortrow(int[][] m, int tid, boolean ascending) {
    }

    private void transpose(int[][] m) {

    }
}
