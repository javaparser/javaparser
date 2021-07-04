public class W {
    public int x;

    class R extends W { }
    class S extends W { }

    //@ public normal_behavior
    //@   requires r != null && s != null;
    public void m(R r, S s) {
        Object rr = r;
        Object ss = s;
        assert rr != ss;  // OpenJML warns about this
        assert !(rr instanceof S);
        assert !(ss instanceof R);
    }

    //@ public normal_behavior
    //@   requires r != null && s != null;
    //@   assignable r.x;
    //@   ensures r.x == 10;
    //@   ensures s.x == \old(s.x);  // OpenJML warns about this
    public void p(R r, S s) {
        r.x = 10;
    }
    
}