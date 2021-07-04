

public class Test {
    
    public void mm() {
        //@ assert A.m() == 1;
        //@ assert B.m() == 2;
        //@ assert C.m() == 3;
    }
    
    public void mq() {
        B b = new B();
        int k = b.mi();  // Inheritance should result in infeasibility
        //@ assert k == 2;
    }
    
}

class A {
    
    //@ ensures \result == 1;
    //@ pure spec_public
    static private int m() {
        return 1;
    }
    //@ public normal_behavior ensures \result == 1;
    //@ pure 
    public int mi() {
        return 1;
    }
}


class B extends A {
    
    //@ ensures \result == 2;
    //@ pure spec_public
    static private int m() {
        return 2;
    }
    //@ also public normal_behavior ensures \result == 2;
    //@ pure
    public int mi() {
        return 2;
    }
}


class C extends B {
    
    //@ ensures \result == 3;
    //@ pure spec_public
    static private int m() {
        return 3;
    }
}