public class LinkedList implements List {

    protected /*@ nullable @*/ LinkedListNonEmpty tail;

    //@ private represents theList = tail==null? \seq_empty: tail.theList;

    public void add (int elem) {
        LinkedListNonEmpty tmp = new LinkedListNonEmpty(elem);
        tmp.tail = this.tail;
        this.tail = tmp;
    }

    public void remFirst () {
        if (empty()) return;
        else tail = tail.tail;
    }

    public boolean empty () {
        return tail == null;
    }

    public int size () {
        return empty()? 0: tail.size();
    }

    public int get (int idx) {
        return tail.get(idx);
    }
}
