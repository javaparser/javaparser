import java.util.ArrayList;

public class ListSeq<E extends Object> implements Seq<E> {

    // Private Mutable State
    private /*@ non_null @*/ final ArrayList<E> list = new ArrayList<E>();

    private Integer pos = 1;
    /*@ private invariant 1 <= pos;
      @ private invariant pos <= length() + 1;
     */

    // Constructor
    public ListSeq( /*@ non_null @*/ E[] elements) {
        for (E element : elements) {
            list.add(element);
        }
    }

    // Interface Seq
    @Override
    public void forth() {
        if (pastEnd()) return;
        pos++;
    }

    @Override
    public Integer pos() {
        if (pastEnd()) throw new IndexOutOfBoundsException("There is no position past the end of the sequence.");
        return pos;
    }

    @Override
    public E current() {
        return list.get(pos-1);
    }

    @Override  //@ pure helper
    public Integer length() {
        return list.size();
    }

    @Override
    public Boolean pastEnd() {
        return pos.equals(length()+1);
    }
}