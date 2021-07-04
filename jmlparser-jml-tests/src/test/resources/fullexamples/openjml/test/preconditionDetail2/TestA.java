 class TestAA extends TestB {
    
    //@ also
    //@   requires p >= 0;
    //@   requires p >= 10;
    //@   requires p >= 20;
    //@ also
    //@   requires p >= 5;
    //@   requires p >= 15;
    //@   requires p >= 25;
    public void m(int p, int q, int r) {
    }
    
}

public class TestA {
    
    
    public static void mm(TestAA a, int i) {
        switch (i) {
        case 1: a.m(100,100,100); break;
        case 2: a.m(15,15,10); break;
        case 3: a.m(0,0,0); break;
        case 4: a.m(0,100,0); break;
        }
    }
}