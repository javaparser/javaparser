public class NullableOld {
    
    //@ old nullable Object o = oo;
    //@ requires o != null;
    public void m(/*@ nullable */ Object oo) {
        
    }
    
    //@ old Object o = oo;
    //@ requires o != null;
    public void mbad(/*@ nullable */ Object oo) {
        
    }
    
    public void mm() {
        m(null);
    }
    
    public void mmm() {
        mbad(null);
    }
}