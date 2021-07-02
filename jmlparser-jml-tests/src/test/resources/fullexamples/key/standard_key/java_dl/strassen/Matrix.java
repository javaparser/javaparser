/** a matrix of size 2^n x 2^n */
final /*@ pure @*/ class Matrix {

    // recursive case for matrices of size > 2
    //@ nullable
    final Matrix a,b,
                 c,d;
    // base case for 2x2 matrix
    final int v11, v12,
	      v21, v22;

    /*@ invariant a==null <==> b==null;
      @ invariant a==null <==> c==null;
      @ invariant a==null <==> d==null;
      @*/

    // create 2x2 matrix
    Matrix (int a, int b,
            int c, int d) {
        this.v11=a; this.v12=b; 
        this.v21=c; this.v22=d;
    }

    // create general matrix
    Matrix (Matrix a, Matrix b,
	    Matrix c, Matrix d) {
        this.a =a; this.b =b;
	this.c =c; this.d =d;
    }

    //@ strictly_pure
    //@ measured_by size();
    public boolean equals(Matrix o) {
	 if (size()==2) {
	     if (o.size()==2) {
                 return (  v11==o.v11 && v12==o.v12
                        && v21==o.v21 && v22==o.v22);
	     } else return false;
	 } else {
             if (o.size()==2)
		 return false;
	     else {
		 return ( a.equals(o.a) && b.equals(o.b)
		       && c.equals(o.c) && d.equals(o.d));
             }
	 }
    }

    //@ strictly_pure
    int size () {
        if (a==null) return 2;
	else return a.size()*2;
    }

    /** matrix addition */
    static Matrix plus (Matrix m, Matrix n) {
	if (m.size()==2) {
	    return new Matrix(m.v11+n.v11, m.v12+n.v12,
			      m.v21+n.v21, m.v22+n.v22);
	} else {
	    return new Matrix(plus(m.a,n.a), plus(m.b,n.b),
			      plus(m.c,n.c), plus(m.d,n.d));
	}
    }

    /** matrix negation */
    static Matrix neg (Matrix m) {
	if (m.size()==2) {
            return new Matrix(-m.v11, -m.v12,
			      -m.v21, -m.v22);
	} else {
	    return new Matrix(neg(m.a), neg(m.b),
			      neg(m.c), neg(m.d));
	}
    }

    /** naive O(n^3) matrix multiplication */
    static Matrix mult (Matrix m, Matrix n) {
	if (m.size()==2) {
            return new Matrix(
                m.v11*n.v11 + m.v12*n.v21,  m.v11*n.v12 + m.v12*n.v12,
                m.v21*n.v11 + m.v22*n.v21,  m.v21*n.v12 + m.v22*n.v22);
	} else {
	    return new Matrix(
	        plus(mult(m.a,n.a),mult(m.b,n.c)), 
		plus(mult(m.a,n.b),mult(m.b,n.d)),
		plus(mult(m.c,n.a),mult(m.d,n.c)),
	        plus(mult(m.c,n.b),mult(m.d,n.d)));
	}
    }

    /** fancy O(n^{log 7}) matrix multiplication by Strassen (base case) */
    /*@ normal_behavior
      @ requires m.size() == 2 && n.size() == 2;
      @ ensures \result.equals(mult(m,n));
      @*/
    static Matrix strassen22 (Matrix m, Matrix n) {
        int m1 = (m.v11+m.v22)*(n.v11+n.v22);
        int m2 = (m.v21+m.v22)*n.v11;
        int m3 = m.v11*(n.v12-n.v22);
        int m4 = m.v22*(n.v21-n.v11);
        int m5 = (m.v11+m.v12)*n.v22;
        int m6 = (m.v21-m.v11)*(n.v11+n.v12);
        int m7 = (m.v12-m.v22)*(n.v21+n.v22);
        return new Matrix(
            m1+m4-m5+m7,  m3+m5,
            m2+m4      ,  m1-m2+m3+m6);
    }

    /** fancy O(n^{log 7}) matrix multiplication by Strassen */
    /*@ normal_behavior
      @ requires m.size() == n.size();
      @ ensures \result.equals(mult(m,n));
      @ measured_by m.size();
      @*/
    static Matrix strassen (Matrix m, Matrix n) {
	if (m.size() == 2) return strassen22(m,n);
        final Matrix m1 = strassen(plus(m.a,m.d),plus(n.a,n.d));
	final Matrix m2 = strassen(plus(m.c,m.d),n.a);
	final Matrix m3 = strassen(m.a,plus(n.b,neg(n.d)));
	final Matrix m4 = strassen(m.d,plus(n.c,neg(n.a)));
	final Matrix m5 = strassen(plus(m.a,m.b),n.d);
	final Matrix m6 = strassen(plus(m.c,neg(m.a)),plus(n.a,n.b));
	final Matrix m7 = strassen(plus(m.b,neg(m.d)),plus(n.c,n.d));
	final Matrix ra = plus(m1,plus(m4,plus(neg(m5),m7)));
	final Matrix rb = plus(m3,m5);
	final Matrix rc = plus(m2,m4);
	final Matrix rd = plus(m1,plus(neg(m2),plus(m3,m6)));
	return new Matrix(ra,rb,rc,rd);
    }
}

