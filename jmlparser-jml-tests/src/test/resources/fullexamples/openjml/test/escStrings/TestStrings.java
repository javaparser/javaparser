
public class TestStrings {
    
    //@ public normal_behavior
    //@   ensures \result == "ABC".equals(s);
    //@ pure
    public static boolean m1(String s) {
        if ("ABC".equals(s)) return true;
        return false;
    }
    
    //@ public normal_behavior
    //@   ensures "ABC".equals(s) ==> \result == 1;
    //@   ensures "ABD".equals(s) ==> \result == 2;
    //@   ensures "DEF".equals(s) ==> \result == 3;
    // @   ensures !("ABC".equals(s)|"ABD".equals(s)|"DEF".equals(s)) ==> \result == -1;
    //@ pure
    public static int m2(String s) {
        switch (s) {
        case "ABC": /*@ assert "ABC".equals(s); */ return 1;
        case "ABD": /*@ assert !"ABC".equals(s); */return 2;
        case "DEF": return 3;
        default: /*@ assert !"ABC".equals(s); */ return -1;
        }
    }
    
    
}