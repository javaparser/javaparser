class B {

    //@ ensures true;
    void m(int[][] array) {

	int row = 0;
	int col = 0;
	int sum = 0;

	/*@ maintaining 0 <= row && row <= array.length && 0 <= col && col <= array[row].length;
	  @ decreases \dl_pair(array.length - row, array[row].length - col);
	  @ assignable \strictly_nothing;
	  @*/
	while(row < array.length) {
	    if(col < array[row].length) {
		sum += array[row][col];
		col ++;
	    } else {
		col = 0;
		row ++;
	    }
	}
    }
}
