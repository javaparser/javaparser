class Triangular {

	/*@ normal_behavior
	  @ requires n >= 0;
	  @ ensures 2*\result == n*(n+1);
	  @ measured_by n;
	  @*/
	int tria (int n) {
		if (n <= 0) return 0;
		else return n+tria(n-1);
	}

}
