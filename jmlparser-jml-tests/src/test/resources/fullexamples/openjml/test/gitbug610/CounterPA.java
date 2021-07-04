public class CounterPA {
    public int[] a = new int[10];
    //@ public invariant a.length > 1;
    public void inc() {
        a[0] = a[0] + 1;
    }
    public void inc0() {
    	a[0]++;
    }
    public void inc2() {
    	a[0] += 1;
    }
    //@ requires a[0] < Integer.MAX_VALUE;
    public void incOK3() {
    	a[0]++;
    }
    //@ requires a[0] < Integer.MAX_VALUE;
    public void incOK4() {
    	a[0] += 1;
    }
}
