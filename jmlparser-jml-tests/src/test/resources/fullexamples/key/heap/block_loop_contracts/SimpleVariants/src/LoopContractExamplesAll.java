
public class LoopContractExamplesAll {

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract_onLoop(int[] arr) {
        int i = 0;
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        while (i < arr.length) {
            ++arr[i];
            ++i;
        }
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract_onBlock(int[] arr) {
        int i = 0;
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        {
            while (i < arr.length) {
                ++arr[i];
                ++i;
            }
        }
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract_forLoop_onLoop(int[] arr) {
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        for (int i = 0; i < arr.length; ++i) {
            ++arr[i];
        }
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @ assignable arr[*];
      @*/
    public static void mapIncrement_loopContract_forLoop_onBlock(int[] arr) {
        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= i && i <= arr.length;
          @ ensures (\forall int j; \before(i) <= j && j < arr.length;
          @         arr[j] == \before(arr[j]) + 1);
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        {
            for (int i = 0; i < arr.length; ++i) {
                ++arr[i];
            }
        }
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures (\forall int i; 0 <= i && i < arr.length;
      @     arr[i] == \old(arr[i]) + 1);
      @*/
    public static void mapIncrement_loopInvariant(int[] arr) {
        int i = 0; 

        /*@ loop_invariant (0 <= i && i <= arr.length)
          @     && (\forall int j; 0 <= j && j < i; arr[j] == \old(arr[j]) + 1)
          @     && (\forall int j; i <= j && j < arr.length;
          @         arr[j] == \old(arr[j]));
          @ assignable arr[i .. arr.length];
          @ decreases arr.length - i;
          @*/
        while (i < arr.length) {
            ++arr[i];
            ++i;
        }
    }
    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onNormalLoop(int[] arr) {
        int sum = 0;

        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= idx && idx <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < idx; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - idx;
          @*/
        for (int idx = 0; idx < arr.length; ++idx) {
            sum += arr[idx];
        }

        return sum;
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onLoop(int[] arr) {
        int sum = 0;

        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= \index && \index <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < \index; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - \index;
          @*/
        for (int el : arr) {
            sum += el;
        }

        return sum;
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopContract_onBlock(int[] arr) {
        int sum = 0;

        /*@ loop_contract normal_behavior
          @ requires arr != null && 0 <= \index && \index <= arr.length;
          @ requires sum == (\sum int i; 0 <= i && i < \index; arr[i]);
          @ ensures  sum == (\sum int i; 0 <= i && i < arr.length; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - \index;
          @*/
        {
            for (int el : arr) {
                sum += el;
            }
        }

        return sum;
    }

    /*@ normal_behavior
      @ requires arr != null;
      @ ensures \result == (\sum int i; 0 <= i && i < arr.length; arr[i]);
      @ assignable arr[*];
      @*/
    public static int sum_loopInvariant(int[] arr) {
        int sum = 0;

        /*@ loop_invariant arr != null && 0 <= \index && \index <= arr.length;
          @ loop_invariant sum == (\sum int i; 0 <= i && i <  \index; arr[i]);
          @ assignable \nothing;
          @ decreases arr.length - \index;
          @*/
        for (int el : arr) {
            sum += el;
        }

        return sum;
    }
}
