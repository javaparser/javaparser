public class FreeConditions {

    public static int field;

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void blockContract0() {
        /*@ public normal_behavior
          @ requires_free field == 41;
          @ ensures field == 42;
          @*/
        {
            ++field;
        }
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void blockContract1() {
        /*@ public normal_behavior
          @ ensures_free field == 42;
          @*/
        {
            ++field;
        }
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void assertions0() {
        //@ assume field == 41;
        ++field;
        //@ assert field == 42;

        ;
    }

    /*@ public normal_behavior
      @ ensures field == 42;
      @*/
    public static void assertions1() {
        //@ assume field == 42;

        ;
    }
}
