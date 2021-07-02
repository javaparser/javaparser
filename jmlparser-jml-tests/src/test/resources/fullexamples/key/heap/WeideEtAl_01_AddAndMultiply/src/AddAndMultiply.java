class AddAndMultiply {
     
    /*@ normal_behaviour
      @   ensures \result == x + y;
      @*/
    /*@pure@*/ int add(int x, int y) {
	int res = x;
	if(y < 0) {
	    /*@ loop_invariant y <= i && i <= 0 && res == x + i; 
	      @ assignable \nothing;
	      @ decreases i - y;
	      @*/
	    for(int i = 0; i > y; i--) {
		res--;
	    }
	} else {
	    /*@ loop_invariant 0 <= i && i <= y && res == x + i; 
	      @ assignable \nothing;
	      @ decreases y - i;
	      @*/
	    for(int i = 0; i < y; i++) {
		res++;
	    }
	}
	return res;
    }
    
    
    /*@ normal_behaviour
      @   measured_by b < 0 ? -b + 1 : b;
      @   ensures \result == a * b;
      @*/
    /*@pure@*/ int mul(int a, int b) {
	if(b == 0) {
	    return 0;
	} else if(b < 0) {
	    return -mul(a, -b);
	} else {
	    return add(a, mul(a, b - 1));
	}
    }
}
