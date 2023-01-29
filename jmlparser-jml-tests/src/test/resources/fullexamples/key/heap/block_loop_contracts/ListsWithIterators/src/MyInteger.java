public final class MyInteger {

    public final int val;

    /*@ public normal_behavior
      @ ensures this.val == val;
      @ assignable \nothing;
      @*/
    public MyInteger(int val) {
        this.val = val;
    }

    /*@ public normal_behavior
      @ ensures \result != null;
      @ ensures \result.val == val;
      @ assignable \nothing;
      @*/
    public static MyInteger valueOf(int val) {
        return new MyInteger(val);
    }

    /*@ public normal_behavior
      @ ensures \result == val;
      @ assignable \strictly_nothing;
      @*/
    public int intValue() {
        return val;
    }
}