//@ code_safe_math spec_bigint_math
public class Test {
    
    int f;
    
    public static int add(int a) {
        return a+1;  // Should issue an overflow error
    }
    public static int inc(int a) {
        return ++a;  // Should issue an overflow error
    }
    public static int dec(int a) {
        return --a;  // Should issue an overflow error
    }
    //@ ensures \result == a;
    public static int incp(int a) {
        return a++;  // Should issue an overflow error
    }
    //@ ensures \result == a;
    public static int decp(int a) {
        return a--;  // Should issue an overflow error
    }
    
    //@ requires aa.length > 10;
    public static int addarray(int[] aa) {
        return aa[0]+1;  // Should issue an overflow error
    }
    //@ requires aa.length > 10;
    public static int incarray(int[] aa) {
        return ++aa[0];  // Should issue an overflow error
    }
    //@ requires aa.length > 10;
    public static int decarray(int[] aa) {
        return --aa[0];  // Should issue an overflow error
    }
    //@ requires aa.length > 10;
    public static int incarrayx(int[] aa) {
        return aa[0]++;  // Should issue an overflow error
    }
    //@ requires aa.length > 10;
    public static int decarrayx(int[] aa) {
        return aa[0]--;  // Should issue an overflow error
    }
    
    public static int add(Test a) {
        return a.f+1;  // Should issue an overflow error
    }
    public static int inc(Test a) {
        return ++a.f;  // Should issue an overflow error
    }
    public static int dec(Test a) {
        return --a.f;  // Should issue an overflow error
    }
    public static int incx(Test a) {
        return a.f++;  // Should issue an overflow error
    }
    public static int decx(Test a) {
        return a.f--;  // Should issue an overflow error
    }
    
    
    
}