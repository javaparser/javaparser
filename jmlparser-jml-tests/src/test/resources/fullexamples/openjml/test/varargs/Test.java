//@ non_null_by_default
public class Test {
    
    //@ public normal_behavior
    //@   ensures \result == oo.length;
    //@ pure
    public int m(Object o, Object ... oo) {
         return oo.length;
    }
    
    //@ public normal_behavior
    //@   requires oo.length > 1;
    //@   requires \nonnullelements(oo);
    //@   ensures \result == oo[0];
    //@ pure
    public Object mk(Object o, Object ... oo) {
        return oo[0];
    }
    
    Object o2 = new Object();
    
    void mm() {
        Object p = mk(1,o2,3);
        //@ assert p == o2;
    }
    
    void mmbad() {
        Object p = mk(1,o2,null);
        //@ assert p == o2;
    }
    
    void mmbad2() {
        Object p = mk(1);
        //@ assert p == o2;
    }
    
    
    void mn() {
        int i = m(1);
        //@ assert i == 0;
        i = m(1,2,3);
        //@ assert i == 2;
    }
    
    
}