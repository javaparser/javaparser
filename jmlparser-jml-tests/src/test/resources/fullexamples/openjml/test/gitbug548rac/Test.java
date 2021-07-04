//@ non_null_by_default
public class Test extends Base {
    
    public static void main(String ... args) {
        Test t = new Test();
        //@ assert t.cget3(30) == 3;  // ERROR
        //@ assert t.get2(20) == 2;  // ERROR
        //@ assert t.get3(30) == 2;   // ERROR
        //@ assert t.get2(2) == 2;
        //@ assert t.get3(3) == 3; 
        try {
        //@ assert t.get(1) == 1;
        } catch (Throwable e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
        try {
        //@ assert t.cget(1) == 1;  // Exception
        } catch (Throwable e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
    }
    
}

class Base implements IFace {
    
    //@ model public pure int get2(int i) { return i; }
    
    //@ requires i == 1;
    //@ model public pure int cget(int i);
    
    //@ requires i == 3;
    //@ model public pure int cget3(int i) { return i; }
    
}

interface IFace {
    
    
    //@ requires i == 1;
    //@ model public pure int get(int i);
    
    //@ requires i == 2;
    //@ model public pure int get2(int i);
    
    //@ requires i == 3;
    //@ model public pure int get3(int i) { return i; }
}

