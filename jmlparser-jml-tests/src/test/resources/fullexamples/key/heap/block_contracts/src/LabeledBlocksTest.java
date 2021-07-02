
public class LabeledBlocksTest {

    /*@ normal_behavior
      @ ensures \result == 42;
      @*/
    public static int foo() {
        int i = 0;

        /*@ normal_behavior
          @ ensures i == 42;
          @*/
        label: {
            i = 42;
        }

        return i;
    }

    /*@ normal_behavior
      @ ensures \result == 42;
      @*/
    public static int bar() {
        int i = 0;

        /*@ loop_contract normal_behavior
          @ requires i <= 42;
          @ ensures i == 42;
          @*/
        label: while(i < 42) {
            ++i;
        }

        return i;
    }

    /*@ normal_behavior
      @ ensures \result == 42;
      @*/
    public static int baz() {
        int i;

        /*@ loop_contract normal_behavior
          @ requires i <= 42;
          @ ensures i == 42;
          @*/
        label: for(i = 0; i < 42; ++i) { }

        return i;
    }
}
