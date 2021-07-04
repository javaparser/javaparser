//@ model import org.jmlspecs.models.JMLObjectBag;

public interface PriorityQueue {
    
    //@ public instance model JMLObjectBag queue; 

    /*@ public normal_behavior
      @  ensures queue.equals(\old(queue).insert(o));
      @  modifies queue;
      @*/
    public void enqueue(/*@non_null@*/ Comparable o);
    
    /*@ public normal_behavior
      @  requires !isEmpty();
      @  ensures \old(queue).has(\result) &&
      @       queue.equals(\old(queue).remove(\result)) &&
      @   (\forall Comparable o; queue.has(o); \result.compareTo(o) <= 0);
      @  modifies queue;
      @*/
    public /*@non_null@*/ Comparable removeFirst();
    
    /*@ public normal_behavior
      @  ensures \result == (queue.isEmpty());
      @*/
    public /*@pure@*/ boolean isEmpty();
    
}