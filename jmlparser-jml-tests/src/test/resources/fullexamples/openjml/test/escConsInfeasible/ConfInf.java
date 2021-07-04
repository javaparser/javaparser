
//@ non_null_by_default
public class ConfInf {

    public static int xx;

    //@ public normal_behavior
    //@   assignable xx;
    public static int inc() { return xx; }
    //@ spec_public
    private final FF yy;

    //@ private normal_behavior
    //@   assignable xx;
    private ConfInf(int x) {
        this.yy = new FF(inc()) {
        };
    }
}

abstract class FF {
    //@ public normal_behavior
    //@ pure
    public FF(int x) {}
}

// This problem was triggered by calling a method in the arguments
// of a constructor, because some values were set before 
// argument evaluation that should ahve been set after.
