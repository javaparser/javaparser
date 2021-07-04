//@ code_bigint_math spec_bigint_math
public class BoxingTests {
	//@ ensures \result == 1;
    public static Integer incr_test() {
        Integer x = 0;
        x++;
        return x;
    }

    public Integer i;
    
    //@ requires b != null;
    //@ requires b.i != null;
    public static void incr_test2(BoxingTests b) {
        b.i++;
        //@ assert b.i == \old(b.i) + 1;
    }

    //@ requires a.length > 1;
    //@ requires a[0] != null;
    //@ requires a[0] == 5;
    public static void incr_test3(Integer[] a) {
        a[0]++;
        //@ assert a[0] == 6;
    }

    //@ ensures \result == false;
    public static Boolean and_test() {
        Boolean b = Boolean.TRUE;
        b &= false;
        return b;
    }
    
    public BoxingTests() { i = 0; }
}

// FIXME - add tests like Short += int, Short += SHort, etc.