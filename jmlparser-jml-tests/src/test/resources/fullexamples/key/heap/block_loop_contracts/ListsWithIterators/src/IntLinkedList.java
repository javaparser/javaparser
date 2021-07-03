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
      @      && ((IntNode)nodeseq[i]).data == (int)seq[i] 
      @      && (\forall int j; 0<=j && j<size; (IntNode)nodeseq[i] == (IntNode)nodeseq[j] ==> i == j)
      @      && ((IntNode)nodeseq[i]).next == (i==size-1 ? null : (IntNode)nodeseq[i+1]));
      @
      @ invariant first == (size == 0 ? null : (IntNode)nodeseq[0]);
      @ invariant last == (size == 0 ? null : (IntNode)nodeseq[size-1]);
      @
      @ invariant size == seq.length && size == nodeseq.length;
      @*/
    
    public IntIterator iterator() {
        return new IntIterator(this);
    }
    
    /*@ public normal_behavior
      @ ensures \result == (\sum int i; 0 <= i && i < seq.length; (int)seq[i]);
      @ assignable \nothing;
      @*/
    public int sum_loopContract() {
        int result = 0;
        
        /*@ loop_contract normal_behavior
          @ requires \invariant_for(this);
          @ ensures \invariant_for(this);
          @ ensures \values.length <= seq.length;
          @ ensures \values == seq[0 .. (\values.length - 1)];
          @ ensures result == (\sum int i; 0 <= i && i < \values.length; (int)seq[i]);
          @ decreases seq.length - \values.length;
          @ assignable \nothing;
          @*/
        for (MyInteger i : this) {
            result += i.intValue();
        }
        
        return result;
    }
    
    /*@ public normal_behavior
      @ ensures \result == (\sum int i; 0 <= i && i < seq.length; (int)seq[i]);
      @ assignable \nothing;
      @*/
    public int sum_loopInvariant() {
        int result = 0;
        
        /*@ loop_invariant true;
          @ decreases seq.length - \values.length;
          @ assignable \nothing;
          @*/
        for (MyInteger i : this) {
            result += i.intValue();
        }
        
        return result;
    }
}
