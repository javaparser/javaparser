package simple_evoting;


public class SMTEnv {

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  Environment.rep;
      @ determines  Environment.result, message_length, sender_id, recipient_id,
      @             port, \result,
      @             ( (\result != null) ? (\seq_def int i; 0; \result.length; \result[i]) : null )
      @       \by   \itself;
      @*/
    //@ helper
    public static /*@ nullable */ byte[] send(int message_length,
                                                           int sender_id,
                                                           int recipient_id,
                                                           Server server,
                                                           int port) {
        Environment.untrustedOutput(7803);
        Environment.untrustedOutput(message_length);
        Environment.untrustedOutput(sender_id);
        Environment.untrustedOutput(recipient_id);
//		Environment.untrustedOutputString(server);
        Environment.untrustedOutput(port);
        return Environment.untrustedInputMessage();
    }
}
