import org.jmlspecs.models.JMLValueSequence;

public class SequenceUtilities {
    public static JMLValueSequence makeSequence() {
        JMLValueSequence seq = new JMLValueSequence();
        //@ assert seq.isEmpty(); // failed to verify even though this is explicitly ensured in the spec for the constructor
//        seq = seq.insertBack(JMLByte.ZERO);
//        //@ assert seq.int_length() == 1; // also failed
        return seq;
    }
}