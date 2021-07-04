
public interface PriorityQueue {
    
    //@ public instance model int size; 

    //@ public invariant size >= 0;
    
    /*@ public normal_behavior
      @  ensures size == \old(size) + 1;
      @*/
    public void enqueue(/*@non_null@*/ Comparable o);
    
    /*@ public normal_behavior
      @  requires !isEmpty();
      @  ensures size == \old(size) - 1;
      @*/
    public /*@non_null@*/ Comparable removeFirst();
    
    /*@ public normal_behavior
      @  ensures \result == (size == 0);
      @*/
    public /*@pure@*/ boolean isEmpty();
    
}
