/** A 2x2 matrix */
final class Matrix22 {

    final int a,b,
              c,d;

    Matrix22 (int a, int b,
            int c, int d) {
        this.a=a; this.b=b; 
        this.c=c; this.d=d;
    }

    //@ strictly_pure
    public boolean equals(Matrix22 o) {
         return ( a==o.a & b==o.b
                & c==o.c & d==o.d);
    }

    /** naive O(n^3) matrix multiplication */
    //@ strictly_pure 
    static Matrix22 mult (Matrix22 m, Matrix22 n) {
        return new Matrix22(
            m.a*n.a + m.b*n.c,  m.a*n.b + m.b*n.d,
            m.c*n.a + m.d*n.c,  m.c*n.b + m.d*n.d);
    }

    /** fancy O(n^{log 7}) matrix multiplication by Strassen */
    /*@ normal_behavior
      @ ensures \result.equals(mult(m,n));
      @*/
    static Matrix22 strassen (Matrix22 m, Matrix22 n) {
        int m1 = (m.a+m.d)*(n.a+n.d);
        int m2 = (m.c+m.d)*n.a;
        int m3 = m.a*(n.b-n.d);
        int m4 = m.d*(n.c-n.a);
        int m5 = (m.a+m.b)*n.d;
        int m6 = (m.c-m.a)*(n.a+n.b);
        int m7 = (m.b-m.d)*(n.c+n.d);
        return new Matrix22(
            m1+m4-m5+m7,  m3+m5,
            m2+m4      ,  m1-m2+m3+m6);
    }

}
