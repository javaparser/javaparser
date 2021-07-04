public class CounterPP {
    protected /*@ spec_public @*/ int count;
    public void inc() {
        count++;
    }
    public void inc2() {
        count += 1;
    }
    //@ requires count < Integer.MAX_VALUE;
    public void incOK3() {
        count++;
    }
    //@ requires count < Integer.MAX_VALUE;
    public void incOK4() {
        count += 1;
    }
    public /*@ pure @*/ int val() {
        return count;
    }
}
