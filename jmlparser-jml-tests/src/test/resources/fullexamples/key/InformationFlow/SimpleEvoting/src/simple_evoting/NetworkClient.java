package simple_evoting;


public class NetworkClient {

    /*@ normal_behavior
      @ ensures     true;
      @ assignable  Environment.rep;
      @ determines  Environment.result, port,
      @             message,
      @             ( (message != null) ? (\seq_def int i; 0; message.length; message[i]) : null )
      @        \by  \itself;
      @*/
    //@ helper
    public static void send(/*@ nullable */ byte[] message,
                            Server server,
                            int port) {
        // input
        Environment.untrustedOutput(0x2301);
        Environment.untrustedOutputMessage(message);
//        Environment.untrustedOutputString(server);
        Environment.untrustedOutput(port);
        // output
//		if ( Environment.untrustedInput()==0 ) throw new NetworkError();
    }
}
