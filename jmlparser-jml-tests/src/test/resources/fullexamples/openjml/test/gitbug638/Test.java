public class Test {
    
    public int x;
    public static int y;
    
    //@ requires x >= 0 && y > 0;
    public Test(int x) {}
    
    //@ requires x >= 0;
    public Test() {}
    
    //@ requires this.x >= 0;
    public Test(boolean b) {}

    //@ requires x >= 0 && y > 0;
    public void m(int x) {}
    
    //@ requires x >= 0;
    public void m() {}
    
    //@ requires this.x >= 0;
    public void m(boolean b) {}
    
    //@ requires t != this;
    public Test(Test t) {}
    
    public Test(double f) {
        this(this);
    }
}