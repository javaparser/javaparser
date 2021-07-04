public class TestB implements TestC {
    
    //@ also
    //@   requires q >= 0 &&  q >= 10 && q >= 20;
    public void m( /*@ non_null */Integer p, int q,  /*@ non_null */Integer r) {
    }

}