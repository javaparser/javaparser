public final class IntLinkedList implements IntList {
        
    /*@nullable@*/ IntNode first;
    /*@nullable@*/ IntNode last;
    int size;

    /*@ ghost \seq nodeseq; */

    /*@
      @ invariant footprint == \set_union(this.*,
      @      (\infinite_union int i; 0<=i && i<size; ((IntNode)nodeseq[i]).*));
      @
      @ invariant (\forall int i; 0<=i && i<size; 
      @         ((IntNode)nodeseq[i]) != null  // this implies \typeof(nodeseq[i]) == \type(IntNode)
      @      && ((IntNode)nodeseq[i]).data == seq[i] 
      @      && (\forall int j; 0<=j && j<size; (IntNode)nodeseq[i] == (IntNode)nodeseq[j] ==> i == j)
      @      && ((IntNode)nodeseq[i]).next == (i==size-1 ? null : (IntNode)nodeseq[i+1]));
      @
      @ invariant first == (size == 0 ? null : (IntNode)nodeseq[0]);
      @ invariant last == (size == 0 ? null : (IntNode)nodeseq[size-1]);
      @
      @ invariant size == seq.length && size == nodeseq.length;
      @*/

    /*@ normal_behavior
      @ ensures (\forall int i; 0 <= i && i < size;
      @     ((int) seq[i]) == \old((int) seq[i]) + 1);
      @ ensures size == \old(size);
      @ assignable \set_union(\singleton(seq), (\infinite_union int j; 0 <= j && j < size; \singleton(((IntNode)nodeseq[j]).data)));
      @*/
    public void mapIncrement_loopContract() {
        IntNode current = first;
        int i = 0;

        /*@ loop_contract normal_behavior
          @ requires \invariant_for(this);
          @ requires 0 <= i && i <= size;
          @ requires i < size ==> current == (IntNode) nodeseq[i];
          @ requires i == size ==> current == null;
          @ ensures \invariant_for(this);
          @ ensures (\forall int j; \before(i) <= j && j < size;
          @     (int) seq[j] == \before((int) seq[j]) + 1);
          @ ensures size == \before(size);
          @ assignable \set_union(\singleton(seq), (\infinite_union int j; i <= j && j < size; \singleton(((IntNode)nodeseq[j]).data)));
          @ decreases nodeseq.length - i;
          @*/
        {
            while (current != null) {
                ++current.data;
                //@ set seq = \seq_concat(\seq_sub(seq, 0, i), \seq_concat(\seq_singleton(current.data), \seq_sub(seq, i+1, size)));
                current = current.next;
                ++i;
            }
        }
    }

    /*@ normal_behavior
      @ ensures (\forall int i; 0 <= i && i < size;
      @     ((int) seq[i]) == \old((int) seq[i]) + 1);
      @ ensures size == \old(size);
      @ assignable \set_union(\singleton(seq), (\infinite_union int j; 0 <= j && j < size; \singleton(((IntNode)nodeseq[j]).data)));
      @*/
    public void mapIncrement_loopInvariant() {
        IntNode current = first;
        int i = 0;

        /*@ loop_invariant \invariant_for(this);
          @ loop_invariant 0 <= i && i <= size;
          @ loop_invariant i < size ==> current == (IntNode) nodeseq[i];
          @ loop_invariant i == size ==> current == null;
          @ loop_invariant (\forall int j; 0 <= j && j < i;
          @     (int) seq[j] == \old((int) seq[j]) + 1);
          @ loop_invariant (\forall int j; i <= j && j < size;
          @     (int) seq[j] == \old((int) seq[j]));
          @ loop_invariant size == \old(size);
          @ assignable \set_union(\singleton(seq), (\infinite_union int j; i <= j && j < size; \singleton(((IntNode)nodeseq[j]).data)));
          @ decreases nodeseq.length - i;
          @*/
        while (current != null) {
            ++current.data;
            //@ set seq = \seq_concat(\seq_sub(seq, 0, i), \seq_concat(\seq_singleton(current.data), \seq_sub(seq, i+1, size)));
            current = current.next;
            ++i;
        }
    }
}
