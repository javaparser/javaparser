public class Byzantine{

    public int[] hs;
    public int[][] matrix;

    public static final int HEALTHY = 0;    
    public static final int FAULTY = 1;
    public static final int ERROR = 2;

    /*@ public normal_behavior
      @  requires \nonnullelements(matrix) &&
      @     matrix.length==hs.length && 
      @     (\forall int i; i>=0 && i<matrix.length; matrix[i].length==hs.length && hs[i]==ERROR && 
      @      hs!=matrix[i]) &&
      @     (\forall int i,j; i>=0 && i<matrix.length && j>=0 && j<matrix[i].length; 
      @         (matrix[i][j]==ERROR || matrix[i][j]==FAULTY || matrix[i][j]==HEALTHY));
      @  assignable hs[*];
      @  ensures (\forall int k; k>=0 && k<matrix.length; 
      @     (\exists int j; j>=0 && j<matrix[k].length; matrix[k][j]==FAULTY)? 
      @          hs[k]==FAULTY : 
      @            ((\bsum int x; 0; matrix[k].length; matrix[k][x]==HEALTHY ? 1 : 0) >=
      @             (\bsum int x; 0; matrix[k].length; matrix[k][x]==ERROR ? 1 : 0)) ?
      @            hs[k]==HEALTHY : hs[k]==FAULTY);
      @*/
    public void computeHealthState(){
	/*@ loop_invariant i>=0 && i<=matrix.length &&
	  @ (\forall int k; k>=0 && k<i; 
	  @     (\exists int j; j>=0 && j<matrix[k].length; matrix[k][j]==FAULTY)? 
	  @          hs[k]==FAULTY : 
	  @            ((\bsum int x; 0; matrix[k].length; matrix[k][x]==HEALTHY ? 1 : 0) >=
	  @             (\bsum int x; 0; matrix[k].length; matrix[k][x]==ERROR ? 1 : 0)) ?
	  @            hs[k]==HEALTHY : hs[k]==FAULTY) && (\forall int j; j>=i && j<hs.length; hs[j]==ERROR);
	  @ assignable i, hs[*];
	  @ decreases matrix.length - i;
	  @*/
	for(int i=0; i<matrix.length; i++){
	    int count_error = 0;
	    int count_healthy = 0;
	    /*@ loop_invariant j>=0 && j<=matrix[i].length && 
	      @   count_healthy == (\bsum int x; 0; j; matrix[i][x]==HEALTHY ? 1 : 0) &&
	      @   count_error == (\bsum int x; 0; j; matrix[i][x]==ERROR ? 1 : 0) &&
	      @   (\forall int k; k>=0 && k<j; matrix[i][k]!=FAULTY);
	      @ assignable j, count_healthy, count_error;
	      @ decreases matrix[i].length - j;
	      @*/
	    for(int j=0; j<matrix[i].length; j++){
		if(matrix[i][j]==FAULTY){
		    hs[i] = FAULTY;
		    break;
		}else if(matrix[i][j]==HEALTHY){
		    count_healthy++;
		}else{
		    count_error++;
		}
	    }
	    if(hs[i]==ERROR && count_healthy >= count_error){
		hs[i] = HEALTHY;
	    }else{
		// This line is missing in the pseudo code, but without it the post-condition
		// can't be established
		hs[i] = FAULTY;
	    }
	}
    }


}
