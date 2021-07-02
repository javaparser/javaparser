package simple_evoting;

public final class Server {

    public final int numberOfVoters;
    public final int numberOfCandidates;
    private /*@ spec_public @*/ final boolean[] ballotCast;  // ballotCast[i]==true iff the i-th voter has already cast her ballot
    /*@ spec_public @*/ final int[] votesForCandidates;


    Server (int n, int m) {
        //@ set rep = \set_union(\all_fields(this), \set_union(\singleton(Setup.numberOfVoters), \singleton(Setup.numberOfCandidates)));
        numberOfVoters = n;
        numberOfCandidates = m;
        ballotCast = new boolean[n];
        votesForCandidates = new int[m];
    }

    /*@ public invariant numberOfVoters == Setup.numberOfVoters;
      @ public invariant numberOfCandidates == Setup.numberOfCandidates;
      @ public invariant ballotCast.length == numberOfVoters;
      @ public invariant votesForCandidates.length == numberOfCandidates;
      @
      @ public ghost \locset rep;
      @ public invariant rep ==
      @     \set_union( this.*, \locset( Setup.numberOfVoters,
      @                                  Setup.numberOfCandidates ) );
      @
      @ accessible \inv: rep;
      @*/


    /**
     * Collects and counts one single ballot.
     */
    /*@ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < numberOfVoters;
      @ requires 0 <= msg.ballot && msg.ballot < numberOfCandidates;
      @ requires ! ballotCast[msg.id];
      @ ensures votesForCandidates[msg.ballot] == \old(votesForCandidates[msg.ballot])+1;
      @ ensures ballotCast[msg.id];
      @ assignable votesForCandidates[msg.ballot], ballotCast[msg.id];
      @
      @ also 
      @
      @ normal_behavior
      @ requires \invariant_for(msg);
      @ requires 0 <= msg.id && msg.id < numberOfVoters;
      @ requires ballotCast[msg.id];
      @ assignable \strictly_nothing;
      @*/
    public void onCollectBallot(Message msg) {
        if (msg == null) return;
        int voterID = msg.id;
        int voteFor = msg.ballot;
        if( voterID<0 || voterID>=numberOfVoters ) return;  // invalid  voter ID
        if( ballotCast[voterID] ) return;  // the voter has already voted
        ballotCast[voterID] = true;
        if (voteFor < 0 || voteFor >= numberOfCandidates ) return;
        else votesForCandidates[voteFor]++;
    }

    /*@ normal_behavior
      @ ensures true;
      @*/
    public /*@ strictly_pure @*/ void onSendResult() {
        final int[] result = getResult();
        // do nothing yet
    }


    /**
     * Returns true if the result is ready, that is if all the eligible voters have already voted.
     */
    /*@ normal_behavior
      @ ensures \result == (\forall int j; 0 <= j && j < numberOfVoters; ballotCast[j]);
      @ accessible rep, ballotCast.*;
      @*/
    public /*@ strictly_pure @*/ boolean resultReady() {
        /*@ loop_invariant 0 <= i && i <= numberOfVoters;
          @ loop_invariant (\forall int j; 0 <= j && j < i; ballotCast[j]);
          @ assignable  \strictly_nothing;
          @ decreases   numberOfVoters-i;
          @*/
        for( int i=0; i<numberOfVoters; i++ ) {
            if( !ballotCast[i] )
                return false;
        }
        return true;
    }

    private /*@ strictly_pure nullable @*/ int[] getResult() {
        if (resultReady())
            return votesForCandidates;
        else return null;
    }
}
