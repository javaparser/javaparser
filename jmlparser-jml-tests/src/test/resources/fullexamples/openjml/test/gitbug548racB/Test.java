//@ non_null_by_default
public class Test extends Base {
    
    public static void main(String ... args) {
        Test t = new Test();
        try {
        //@ assert t.get(1) == 1;
        } catch (Throwable e) {
            System.out.println(e);
            e.printStackTrace(System.out);
        }
    }
    
}

class Base implements IFace {
}

interface IFace {
    
    
    //@ requires i == 1;
    //@ model public pure int get(int i);
    
}

