class Ackermann {


    /*@ normal_behavior
      @ requires 0 <= m && 0 <= n;
      @ ensures \result >= 0;
      @ measured_by m,n;
      @*/
    int a (int m, int n) {
        if ( m==0 ) return n+1;
        else if ( n==0 ) return a(m-1,1);
        else return a(m-1,a(m,n-1));
    }
}
