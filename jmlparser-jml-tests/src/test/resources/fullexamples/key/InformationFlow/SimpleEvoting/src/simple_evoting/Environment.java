package simple_evoting;


public class Environment {

    private /*@ spec_public */ static boolean result; // the LOW variable


    //@ public static model \locset rep;
    //@ public static represents rep = \locset(result);
    //@ accessible rep : \locset(result);
    
    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result, \result \by Environment.result;
      @*/
    //@ helper
    public static native int untrustedInput(); // Declared underspecified method as native

    /*@ normal_behavior
      @ ensures     0 <= \result && \result < x;
      @ assignable  rep;
      @ determines  Environment.result, \result \by Environment.result, x;
      @*/
    //@ helper
    public static native int untrustedInput(int x); // Declared underspecified method as native

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result \by Environment.result, x;
      @*/
    //@ helper
    public static void untrustedOutput(int x) {
        // under specified
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @        \by  Environment.result;
      @*/
    //@ helper
    public static /*@ nullable */ byte[] untrustedInputMessage() {
        int len = untrustedInput();
        if (len < 0) {
            return null;
        }
        byte[] returnval = null;
        /*@ normal_behavior
          @ requires    len >= 0;
          @ ensures     returnval != null && \fresh(returnval);
          @ ensures     returnval.length == len;
          @ assignable  \nothing;
          @ determines  Environment.result, returnval
          @        \by  Environment.result, len
          @        \new_objects returnval;
          @*/
        { returnval = new byte[len]; }
        return untrustedInputMessage(returnval);
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep, returnval[*];
      @ determines  Environment.result, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @        \by  Environment.result, returnval;
      @*/
    //@ helper
    public static byte[] untrustedInputMessage(byte[] returnval) {
        /*@ loop_invariant 0 <= i && i <= returnval.length;
          @ loop_invariant returnval != null && returnval == \old(returnval);
          @ assignable rep, returnval[*];
          @ decreases returnval.length - i;
          @ determines Environment.result, returnval,
          @            (\seq_def int j; 0; i; returnval[j]), i
          @        \by \itself;
          @*/
        for (int i = 0; i < returnval.length; i++) {
            returnval[i] = (byte) Environment.untrustedInput();
        }
        return returnval;
    }


    /*@ normal_behavior
      @ ensures     true;
      @ assignable  rep;
      @ determines  Environment.result
      @        \by  Environment.result, t,
      @             ( (t != null) ? (\seq_def int i; 0; t.length; t[i]) : null );
      @*/
    //@ helper
    public static void untrustedOutputMessage(/*@ nullable */ byte[] t) {
        if (t == null) {
            return;
        }
        untrustedOutput(t.length);
        /*@ loop_invariant 0 <= i && i <= t.length && t != null;
          @ assignable rep;
          @ decreases t.length - i;
          @ determines Environment.result, t, (\seq_def int i; 0; t.length; t[i]), i
          @        \by \itself;
          @*/
        for (int i = 0; i < t.length; i++) {
            untrustedOutput(t[i]);
        }
    }
}
