/**
 * Information flow example.
 *
 * The example is a toy implementation of a voting process. The vote of every
 * voter is read and send over a not further modelled network. If the read
 * vote is not valid, then 0 is send instead to indicate abstention. The votes
 * itself and whether a vote is valid is secrete. At the end the
 * participation is output.
 *
 * Without the optimisations described in the FM-Paper the verification of
 * the method secure_voting() with the help of self-composition is very
 * expensive or even infeasible.
 *
 * @author Christoph Scheben
 */
public class Voter {
    public static int low_outputStream;
    public static boolean low_outputStreamAvailable;
    private static int high_inputStream;

    public static final int low_NUM_OF_VOTERS = 763;
    public static int low_numOfVotes;
    public boolean low_sendSuccessful;
    
    private boolean high_voteValid;
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful
               \by \itself;    @*/
    void secure_voting() {
        /*@ loop_invariant 0 <= i && i <= low_NUM_OF_VOTERS;
            loop_invariant \invariant_for(this);
            determines low_outputStream,
                       low_outputStreamAvailable,
                       low_NUM_OF_VOTERS,
                       low_numOfVotes,
                       low_sendSuccessful,
                       i
                   \by \itself;
            decreases low_NUM_OF_VOTERS - i;
            assignable \everything;
            @*/
        for (int i = 0; i < low_NUM_OF_VOTERS; i++) {
            int high_vote = inputVote();
            /*@ normal_behavior
                determines low_outputStream,
                           low_outputStreamAvailable,
                           low_NUM_OF_VOTERS,
                           low_numOfVotes,
                           low_sendSuccessful
                       \by \itself;    @*/
            {   if (isValid(high_vote)) {
                    high_voteValid = true;
                    low_sendSuccessful = sendVote(high_vote);
                } else {
                    high_voteValid = false;
                    low_sendSuccessful = sendVote(0);
                }
            }
            /*@ normal_behavior
                determines low_outputStream,
                           low_outputStreamAvailable,
                           low_NUM_OF_VOTERS,
                           low_numOfVotes,
                           low_sendSuccessful
                       \by \itself;    @*/
            { low_numOfVotes = (low_sendSuccessful ? low_numOfVotes + 1 : low_numOfVotes); }
        }
        publishVoterParticipation();
    }
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful
               \by \itself;    @*/
    int inputVote() {
        return high_inputStream;
    }
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful,
                   \result
               \by \itself;               @*/
    boolean sendVote(int x) {
        if (low_outputStreamAvailable) {
            // encrypt and send over some channel (not further modeled here)
            return true;
        } else {
            return false;
        }
    }
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful
               \by \itself;    @*/
    boolean isValid(int high_vote) {
        // vote has to be in range 1..255
        return 0 < high_vote && high_vote <= 255;
    }
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful
               \by \itself;    @*/
    void publishVoterParticipation() {
        low_outputStream = low_numOfVotes * 100 / low_NUM_OF_VOTERS;
    }
    
    
    /*@ normal_behavior
        determines low_outputStream,
                   low_outputStreamAvailable,
                   low_NUM_OF_VOTERS,
                   low_numOfVotes,
                   low_sendSuccessful
               \by \itself;    @*/
    void insecure_voting() {
        int high_vote = inputVote();
        // vote has to be in range 1..255
        if (0 < high_vote && high_vote <= 255) {
            low_sendSuccessful = sendVote(high_vote);
            low_numOfVotes++;
        } else {
            high_vote = 0;
            low_sendSuccessful = sendVote(high_vote);
        }
        publishVoterParticipation();
    }
}
