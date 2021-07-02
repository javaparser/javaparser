package simple_evoting;

public final class Voter {

    private /*@ spec_public @*/ final int id;
    /*@ spec_public @*/ final int vote;


    Voter (int id, int vote) {
        this.id = id;
        this.vote = vote;
    }

    /*@ public invariant 0 <= vote && vote < Setup.numberOfCandidates;
      @ public invariant 0 <= id && id < Setup.numberOfVoters;
      @ accessible \inv: this.*, Setup.numberOfCandidates,
      @                  Setup.numberOfVoters;
      @*/


    /*@ normal_behavior
      @ requires ! server.ballotCast[id];
      @ requires \invariant_for(server);
      @ ensures server.votesForCandidates[vote] == \old(server.votesForCandidates[vote])+1;
      @ ensures server.ballotCast[id];
      @ assignable server.votesForCandidates[vote], server.ballotCast[id],
      @            Environment.rep;
      @ determines Environment.result \by \itself;
      @ also normal_behavior
      @ requires server.ballotCast[id];
      @ requires \invariant_for(server);
      @ ensures  \old(server.votesForCandidates[vote]) == server.votesForCandidates[vote];
      @ ensures  \old(server.ballotCast[id]) == server.ballotCast[id];
      @ assignable Environment.rep;
      @ determines Environment.result \by \itself;
      @*/
    public void onSendBallot(Server server) {
        Message message = new Message(id, vote);
        //@ set message.source = this;
        SMT.send(message, id, server);
    }
}
