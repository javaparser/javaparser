//@ pure
public class JMLStringTestBad {

    //@ model public static void conversionBad4(nullable String s, Object o) {
    //@   ghost string s4 = o; // error
    //@}

    //@ model public static void conversionBad4b(nullable String s, Object o) {
    //@   ghost string s4 = (string)o; // error
    //@}

    //@ model public static void conversionBad5(nullable String s, Object o) {
    //@   ghost string s5 = null; // error
    //@}

    //@ model public static void conversionBad6(string s1) {
    //@   ghost string s6 = (string)null; // error
    //@}

    //@ model public static void conversionBad7(string s1) {
    //@   ghost Object o1 = s1; // error
    //@}

    //@ model public static void conversionBad8(string s1) {
    //@   ghost Object o1 = (Object)s1; // error
    //@}

}
