//Example from Fig. 8.1
class A {
    private int i = 1;
    /*@ instance invariant i>0 && i<=42; */

    public int getI() { return i; }
    /*@ requires p>0;
      @ ensures i==p;
      @*/
    public void setI(int p) { i=p; }
    public void m1() {
        setI(0);
        i=1;                        
    }
    public void m2() {
        i=0;
        setI(1);                    
    }
    public int m3() {
        i=0;
        i=(new B()).m5(this);       
	return i;
   }
    /*@ ensures \result>0; @*/
    public int m4() {
        return 42/i;
    }
}

class B {
    /*@ ensures \result>0; @*/
    public int m5(A a) {              
        if (a.getI()<=0) a.setI(1);
        return a.m4();                  
    }
}
