     
    public class TransposeMatrixOrig
    {
       //@ requires matrix.length > 0;
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[k] != null);
       //@ requires (\forall int k; 0 <= k && k < matrix.length; matrix[0].length == matrix[k].length);
       //@ ensures (\forall int i, j; i >= 0 && j >= 0 && i < matrix.length && j < matrix[0].length; matrix[i][j] == \result[j][i]);
       //@ ensures matrix.length == \result[0].length;
       //@ ensures matrix[0].length == \result.length;	
       public int[][] transposeMat(int[][] matrix)
       {
          int m, n, p, q;

          m = matrix.length;
          n = matrix[0].length;
     
          int transpose[][] = new int[n][m];
          //@ assume \forall int i; 0<=i<n; transpose[i] != null && transpose[i].length == m;
          //@ assume \forall int i; 0<=i<n; \forall int j; 0<=j<n; i != j ==> transpose[i] != transpose[j];

          //@ assert transpose.length == n;
          //@ assert (\forall int k; 0 <= k && k < n; transpose[k] != null && transpose[k].length == m);
	  //@ maintaining (\forall int i, j; i >= 0 && j >= 0 && i < c && j < n ; matrix[i][j] == transpose[j][i]);
          //@ maintaining c >= 0 && c <= m;
	  //@ decreases m - c;
          for (int c = 0; c < m; c++){
	     //@ maintaining (\forall int j; 0 <= j && j < d; matrix[c][j] == transpose[j][c]);
             //@ maintaining (\forall int k; 0 < k && k < matrix.length; matrix[k].length == n);
             //@ maintaining transpose.length == n;
             //@ maintaining (\forall int k; 0 < k && k < transpose.length; transpose[k].length == m);
	     //@ maintaining 0 <= d && d <= n;
	     //@ decreases n - d;
             //@ maintaining d < n ==> (transpose[d].length == m);
	     //@ maintaining 0 <= c && c < m;
             for (int d = 0; d < n; d++) {
	     //@ assert d < transpose.length && transpose.length == n; 
	     //@ assert d >= 0;
	     //@ assert c <  transpose[0].length && transpose[0].length == m;  
		
             transpose[d][c] = matrix[c][d];  
	     //@ assert transpose[d][c] == matrix[c][d];              
             }
          }
	  return transpose;
       }
    }
