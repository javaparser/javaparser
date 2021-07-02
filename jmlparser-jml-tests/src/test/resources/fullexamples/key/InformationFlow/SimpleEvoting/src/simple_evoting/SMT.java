package simple_evoting;


/**
 *
 * @author christoph
 */
public final class SMT {


    /*@ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < server.numberOfVoters;
      @ requires 0 <= msg.ballot && msg.ballot < server.numberOfCandidates;
      @ requires ! server.ballotCast[msg.id];
      @ requires \invariant_for(server);
      @ ensures server.votesForCandidates[msg.ballot] == \old(server.votesForCandidates[msg.ballot])+1;
      @ ensures server.ballotCast[msg.id];
      @ assignable server.votesForCandidates[msg.ballot], server.ballotCast[msg.id],
      @            Environment.rep;
      @ determines Environment.result \by \itself;
      @
      @ also
      @
      @ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < server.numberOfVoters;
      @ requires server.ballotCast[msg.id];
      @ requires \invariant_for(server);
      @ assignable Environment.rep;
      @ determines Environment.result \by \itself;
      @*/
    //@ helper
    public static void send(Message msg,
                     int senderID,
                     Server server) {
        byte[] output_message =
                SMTEnv.send(/*msg.length*/1, /*senderID*/ 0, /*recipient.ID*/ 0, server, /*port*/ 0);
        server.onCollectBallot(msg);
        NetworkClient.send(output_message, server, /*port*/ 0);
    }
}
