public class Arrays {

    private String[] a;

    //@ ensures true;
    public Object[] get() { return a; }

    //@ requires a.length > 0;
    public String head() { return a[0]; }
    
    //@ requires x.length > 0;
    public Object[][][] head (Object[][][][] x) { return x[0]; } 

    //@ requires a == o && o != null;
    //@ ensures \invariant_for(this);
    //@ helper
    public void unprovable (/*@ nullable @*/ Object o) {}
}
