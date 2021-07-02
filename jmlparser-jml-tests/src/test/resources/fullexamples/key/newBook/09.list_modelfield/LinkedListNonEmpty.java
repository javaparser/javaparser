final class LinkedListNonEmpty extends LinkedList {

    private int head;

    /*@ private represents theList =
      @     \seq_concat (\seq_singleton(head),
      @                  tail==null? \seq_empty: tail.theList);
      @*/

    LinkedListNonEmpty (int elem) { head = elem; }

    public boolean empty () { return false; }

    public int size () {
        return 1+(tail==null? 0: tail.size());
    }

    public int get (int idx) {
        if (idx == 0) return head;
        else return tail.get(idx-1);
    }
}
