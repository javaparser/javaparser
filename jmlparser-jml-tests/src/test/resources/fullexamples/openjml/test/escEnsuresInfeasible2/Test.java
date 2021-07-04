public class Test {
    

    //@ public normal_behavior // Avoids bit arithmetic
    //@   ensures \result == \bigint_math(i < 0 ? ((long)i - Integer.MIN_VALUE - Integer.MIN_VALUE) : i);
    //@   ensures 0 <= \result && \result <= Integer.MAX_UNSIGNED_INT;
    //@ pure helper function // FIXME - causes infeasibility if written as a function with separated ensures conjuncts
    public static long toUnsignedLongBuggy(int i) { return 0xffff_ffffL & i; }

    //@ public normal_behavior
    //@   old long msecs = 1000 * toUnsignedLongBuggy(seconds);
    //@   requires msecs < 1000000;
    //@   ensures \result == msecs;
    //@ pure code_java_math spec_safe_math
    //  @ skipesc
    public static long fromSecondsBuggy(int seconds) {
        long t = 1000 * toUnsignedLongBuggy(seconds);
        //@ assert t < 1000000;
        return t;
    }

}