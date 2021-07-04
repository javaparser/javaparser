//@ nullable_by_default
public class Test {
    public int f;
    
    //@ recommends o != null else NullPointerException;
    public void m1(Test o) {
       if (o == null) throw new NullPointerException();
    }
    
    //@ recommends o != null else NullPointerException;
    public void m2(Test o) {
       o.f = 1;
    }
    
    //@ requires i >= 0;
    //@ recommends o != null else NullPointerException;
    //@ recommends i < 10 else ArrayIndexOutOfBoundsException;
    public void m3(Test o, int i) {
        int[] a = new int[10];
        o.f = a[i];
    }
    
    //@ recommends o != null else NullPointerException;
    //@ recommends i != null else NullPointerException;
    public void m4(Test o, Test i) {
        int k = o.f + i.f;
    }
    
    //@ recommends o != null else NullPointerException;
    //@ recommends i != null else RuntimeException;
    public void m5(Test o, Test i) {
        if (i == null) throw new RuntimeException();
        int k = o.f + i.f;
    }
    
    //@ recommends o != null else RuntimeException;
    //@ recommends i != null else NullPointerException;
    public void m6(Test o, Test i) {
        if (o == null) throw new RuntimeException();
        int k = o.f + i.f;
    }
    
    //@ recommends o != null else RuntimeException;
    public void m7(Test o, Test i) {
        int k = o.f + 1;
    }
    
    //@ recommends o != null else RuntimeException;
    //@ recommends i != null else NullPointerException;
    public void m8(Test o, Test i) {
        int k = o.f + i.f;
    }
    
    //@ recommends o != null else NullPointerException;
    //@ recommends i != null else NullPointerException;
    //@ ensures 0 <= o.f < 10 && i.f < 10 ==> \result < 20;
    public int m9(Test o, Test i) {
        return o.f + i.f;
    }
    
}