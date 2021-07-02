class Saddleback {

    /*@ public normal_behaviour
      @ requires (\forall int i; 0<=i && i<array.length; 
      @     array[i].length == array[0].length);
      @
      @ requires array.length > 0;
      @ requires array[0].length > 0;
      @
      @ requires (\forall int k,i,j;
      @    0<=k && k < i && i < array.length && 0<=j && j < array[0].length;
      @      array[k][j] <= array[i][j]);
      @ 
      @ requires (\forall int k,j,i;
      @    0<=i && i < array.length && 0<=k && k<j && j < array[i].length;
      @      array[i][k] <= array[i][j]);
      @
      @ ensures \result == null ==> 
      @     (\forall int i; 0<=i && i<array.length;
      @       (\forall int j; 0<=j && j<array[i].length;
      @         array[i][j] != value));
      @
      @ ensures \result != null ==>
      @     \result.length == 2 &&
      @     array[\result[0]][\result[1]] == value;
      @ 
      @ modifies \nothing;
      @*/
    public /*@nullable*/ int[] search(int[][] array, int value) {
	int x = 0;
	int y = array[0].length - 1;

	/*@
	  @ loop_invariant
	  @   0 <= x && x <= array.length &&
	  @  -1 <= y && y < array[0].length &&
	  @   (\forall int j,i; 0<=i && i < array.length && 
	  @                     0<=j && j < array[0].length ;
	  @      (i < x || j > y) ==> array[i][j] != value);
	  @
	  @ decreases array.length - x + y;
	  @ modifies \nothing;
	  @*/
	while(x < array.length && y >= 0) {

	     if(array[x][y] == value) {
	    		return new int[] { x, y };
	    }

	     if(array[x][y] < value) {
	     	x++;
	     } else {
	     	y--;
	     }

	}

	return null;
    }
}
