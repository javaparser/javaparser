import java.util.Iterator;

public class IntIterator implements Iterator {

    private final IntLinkedList list;
    private /*@nullable@*/ IntNode next;

    //@ ghost \seq nodeseq;
    //@ ghost \seq seq;

    //@ public instance invariant nodeseq == list.nodeseq[0 .. nodeseq.length];
    //@ public instance invariant seq == list.seq[0 .. seq.length];

    //@ public instance invariant nodeseq.length <= list.nodeseq.length;
    //@ public instance invariant seq.length <= list.seq.length;
    //@ public instance invariant seq.length == nodeseq.length;

    //@ public instance invariant next != null ==> next == (IntNode)list.nodeseq[nodeseq.length];
    //@ public instance invariant next != null ==> next.data == (int)list.seq[seq.length];

    //@ public instance invariant seq.length == list.seq.length <==> next == null;

    /*@ public normal_behavior
      @ requires \invariant_for(list);
      @ ensures \invariant_for(list);
      @ ensures this.list == list;
      @ ensures this.next == list.first;
      @ ensures seq.length == 0;
      @ assignable \nothing;
      @*/
    public IntIterator(IntLinkedList list) {
        this.list = list;
        next = list.first;
    }

    /*@ public normal_behavior
      @ ensures \result == (next != null);
      @ assignable \strictly_nothing;
      @*/
    public boolean hasNext() {
        return next != null;
    }

    /*@ public normal_behavior
      @ requires next != null;
      @ requires \invariant_for(list);
      @ ensures \invariant_for(list);
      @ ensures \result != null;
      @ ensures \result.intValue() == \old(next).data;
      @ ensures seq.length == \old(seq.length) + 1;
      @ assignable next, nodeseq, seq;
      @
      @ also
      @
      @ public exceptional_behavior
      @ requires next == null;
      @ signals(NullPointerException) true;
      @ assignable \nothing;
      @*/
    public MyInteger next() {
        int result = next.data;

        //@ set nodeseq = \seq_concat(nodeseq, \seq_singleton(next));
        //@ set seq = \seq_concat(seq, \seq_singleton(next.data));
        next = next.next;

        return MyInteger.valueOf(result);
    }
}
