//@ model import org.jmlspecs.models.JMLObjectBag;

public class Heap implements PriorityQueue {
    private Comparable[] elems; //@ in queue;
    private int numElems;       //@ in queue;

    /*@ private represents queue = computeQueue(); @*/

    /*@ private invariant elems != null;
      @ private invariant \typeof(elems) == \type(Comparable[]);
      @ private invariant elems.length > 0;
      @ private invariant 0 <= numElems && numElems <= elems.length;
      @ private invariant
      @   (\forall int i; 0 <= i && i < numElems; elems[i] != null);
      @
      @ private invariant
      @   (\forall int i; 0 <= i && i < numElems; 
      @     (2*i+1 < numElems ==> elems[i].compareTo(elems[2*i+1]) <= 0)
      @  && (2*i+2 < numElems ==> elems[i].compareTo(elems[2*i+2]) <= 0));
      @*/

    public Heap() {
	elems = new Comparable[5];
	numElems = 0;
    }

    /*@
    private normal_behavior
      requires elems != null && elems.length > 0;
      requires 0 <= numElems <= elems.length;
      requires (\forall int i; 0 <= i < numElems; elems[i] != null);
    private model pure helper non_null JMLObjectBag computeQueue() {
	JMLObjectBag bag = new JMLObjectBag();
	for (int i= 0; i < numElems; i++)
	    bag = bag.insert(elems[i]);
	return bag;
    }
    @*/
    

    /*@ ensures elems.length > \old(elems.length)
      @       && numElems == \old(numElems);
      @ modifies queue;
      @*/
    private void grow() {
	Comparable[] newElems = new Comparable[elems.length*2];
	System.arraycopy(elems, 0, newElems, 0, elems.length);
	elems = newElems;
    }

    public void enqueue(Comparable o) {
	if (numElems >= elems.length)
	    grow();
	int pos = numElems++;
	int parent = (pos) / 2;
	while (pos > 0 && elems[parent].compareTo(o) > 0) {
	    elems[pos] = elems[parent];
	    pos = parent;
	    parent = (pos) / 2;
	}
	elems[pos] = o;
    }

    public Comparable removeFirst() {
	Comparable first = elems[0];
	Comparable last = elems[--numElems];
	int pos = 0;
	int child = 2*pos+1;
	while (child < numElems) {
	    if (child + 1 < numElems
		&& elems[child].compareTo(elems[child+1]) > 0) {
		child++;
	    }

	    if (elems[child].compareTo(last) > 0)
		break;

	    elems[pos] = elems[child];
	    pos = child;
	    child = 2*pos+1;
	}
	elems[pos] = last;
	return first;
    }

    public boolean isEmpty() {
	return numElems == 0;
    }

    public String toString() {
	StringBuffer sb = new StringBuffer("Heap[");
	String comma = "";
	for (int i = 0; i < numElems; i++) {
	    sb.append(comma).append(elems[i]);
	    comma=",";
	}
	return sb.append("]").toString();
    }
}
