package simple_evoting;

public final class Message {

    public final int id;
    public final int ballot;
    //@ public ghost Voter source;

    //@ public invariant source.id == id;
    //@ public invariant 0 <= id && id < Setup.numberOfVoters;
    //@ accessible \inv : this.*, Setup.numberOfVoters, source.id;

    public Message (int id, int ballot) {
        this.ballot = ballot;
        this.id = id;
    }

}
