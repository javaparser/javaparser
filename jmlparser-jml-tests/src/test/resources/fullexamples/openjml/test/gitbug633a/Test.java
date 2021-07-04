public class Test {
    /*
     Z3 non-deterministically crashes on mfails. Seems OK when the method is
     split between m() and mmod().
    public void mfails() {
        double d = 2.0;
        double dd = 3.0;
        assert d + dd == 5.0;
        assert d + dd != 0.0;
        assert d - dd == -1.0;
        assert d * dd == 6.0;
        assert dd / d == 1.5;
        assert dd % d == 1.0;
        assert (-dd) % d == -1.0;
        assert dd % (-d) == 1.0;
        assert (-dd) % (-d) == -1.0;
    }
    */
    
    public void m() {
        double d = 2.0;
        double dd = 3.0;
        assert d + dd == 5.0;
        assert d + dd != 0.0;
        assert d - dd == -1.0;
        assert d * dd == 6.0;
        assert dd / d == 1.5;
    }
    
    public void mm() {
        
        double d = 2;
        assert d != -1;
    }
    
    public void mmm() {
        
        double d = 2;
        double dd = 3;
        assert d + dd == 5;
        assert d + dd != 0;
        assert d - dd == -1;
        assert d * dd == 6;
        assert dd / d == 1.5;
    }
    public void mmod() {
        
        double d = 2;
        double dd = 3;
        assert dd % d == 1.0;
        assert (-dd) % d == -1;
        assert dd % (-d) == 1;
        assert (-dd) % (-d) == -1.0;
    }
}