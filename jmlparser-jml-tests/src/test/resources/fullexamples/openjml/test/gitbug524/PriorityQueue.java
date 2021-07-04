//@ model import org.jmlspecs.models.JMLObjectBag;

public abstract class PriorityQueue {
    
    //@ public instance model JMLObjectBag queue; 
	//@ public represents queue = computeQueue();
	//@ helper pure
	public abstract JMLObjectBag computeQueue();

    /*@ public normal_behavior
      @  ensures queue.equals(\old(queue).insert(o));
      @*/
    public abstract void enqueue(/*@non_null@*/ Comparable o);
    
    /*@ public normal_behavior
      @  requires !isEmpty();
      @  ensures \old(queue).has(\result) &&
      @       queue.equals(\old(queue).remove(\result)) &&
      @   (\forall Comparable o; queue.has(o); \result.compareTo(o) <= 0);
      @*/
    public abstract /*@non_null@*/ Comparable removeFirst();
    
    /*@ public normal_behavior
      @  ensures \result == (queue.isEmpty());
      @*/
    public abstract /*@pure@*/ boolean isEmpty();
    
}
