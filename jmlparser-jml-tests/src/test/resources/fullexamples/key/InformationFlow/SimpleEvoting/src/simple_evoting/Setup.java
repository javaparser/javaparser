package simple_evoting;

public final class Setup {

    private /*@ spec_public @*/ static Voter[] voters;
    private /*@ spec_public @*/ static Server server;
    private /*@ spec_public @*/ static int numberOfVoters;
    private /*@ spec_public @*/ static int numberOfCandidates;

    private /*@ spec_public nullable */ static int[] out;


    /*@ invariant \nonnullelements(voters);
      @ invariant server != null && \invariant_for(server);
      @ invariant voters.length == numberOfVoters;
      @ invariant (\forall int i; 0 <= i && i < voters.length; voters[i].id == i);
      @ invariant (\forall int i; 0 <= i && i < voters.length; \invariant_for(voters[i]));
      @ accessible \inv: numberOfVoters, numberOfCandidates,
      @                  server, server.rep, voters, voters.*,
      @                  (\infinite_union int i; (0 <= i && i < voters.length) ? voters[i].* : \empty);
      @*/

    /*@ normal_behavior
      @ requires (\forall int j; 0 <= j && j < numberOfVoters; !server.ballotCast[j]);
      @ requires (\forall int i; 0 <= i && i < numberOfCandidates; server.votesForCandidates[i]==0);
      @ ensures (\forall int i; 0 <= i && i < numberOfCandidates;
      @              server.votesForCandidates[i] ==
      @                  (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @ diverges true;
      @ assignable  server.ballotCast[*], server.votesForCandidates[*],
      @             Environment.rep, out;
      @ determines  Environment.result \by Environment.result, numberOfVoters;
      @ determines  out, (\seq_def int i; 0; out.length; out[i])
      @        \by  numberOfCandidates, numberOfVoters, server.votesForCandidates
      @             \declassifies (\seq_def int i; 0; numberOfCandidates;
      @                               (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @*/
    public void main () {
        boolean resultReady = server.resultReady();
        /*@ maintaining \invariant_for(this);
          @
          @   // votes for candidates are sums from voters already voted
          @ maintaining (\forall int i; 0 <= i && i < numberOfCandidates;
          @                  server.votesForCandidates[i] ==
          @                      (\num_of int j; 0 <= j && j < numberOfVoters; server.ballotCast[j] && voters[j].vote == i));
          @
          @ maintaining resultReady == (\forall int j; 0 <= j && j < numberOfVoters; server.ballotCast[j]);
          @
          @ assignable server.ballotCast[*], server.votesForCandidates[*],
          @            Environment.rep;
          @ determines Environment.result, resultReady, numberOfVoters,
          @            (\seq_def int i; 0; numberOfVoters; server.ballotCast[i])
          @        \by \itself;
          @*/
        while ( !resultReady ) { // possibly infinite loop
            // let adversary decide send order
            final int k = Environment.untrustedInput(voters.length);
            final Voter v = voters[k];
            v.onSendBallot(server);
            resultReady = server.resultReady();
        }
        publishResult();
    }


    /*@ normal_behavior
      @ requires (\forall int i; 0 <= i && i < numberOfCandidates;
      @              server.votesForCandidates[i] ==
      @                  (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @ assignable out;
      @ determines  out, (\seq_def int i; 0; out.length; out[i])
      @        \by  numberOfCandidates, numberOfVoters, server.votesForCandidates
      @             \declassifies (\seq_def int i; 0; numberOfCandidates;
      @                               (\num_of int j; 0 <= j && j < numberOfVoters; voters[j].vote == i));
      @*/
    private void publishResult () {
        out = server.votesForCandidates;
    }

}
