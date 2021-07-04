//@ model import org.jmlspecs.models.JMLObjectBag;

public class Heap implements PriorityQueue {
    private Comparable[] elems; //@ in queue;
    private int numElems;       //@ in queue;

    //@ private ghost non_null JMLObjectBag ghostQueue; in queue;
    //@ private represents queue <- ghostQueue;

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
	//@ set ghostQueue = new JMLObjectBag();
    }    

    /*@ ensures elems.length > \old(elems.length)
      @       && numElems == \old(numElems);
      @ modifies queue;
      @*/
    private void grow() {
	Comparable[] newElems = new Comparable[elems.length*2];
	System.arraycopy(elems, 0, newElems, 0, elems.length);
	elems = newElems;
    }

    public void enqueue(/*@non_null@*/ Comparable o) {
	//@ set ghostQueue = ghostQueue.insert(o);
	if (numElems >= elems.length)
	    grow();
	int pos = numElems++;
	int parent = (pos - 1) / 2;
	while (pos > 0 && elems[parent].compareTo(o) > 0) {
	    elems[pos] = elems[parent];
	    pos = parent;
	    parent = (pos - 1) / 2;
	}
	elems[pos] = o;
    }

    public /*@non_null@*/ Comparable removeFirst() {
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
	//@ set ghostQueue = ghostQueue.remove(first);
	return first;
    }

    public /*@pure@*/ boolean isEmpty() {
	return numElems == 0;
    }

    public /*@non_null@*/ String toString() {
	StringBuffer sb = new StringBuffer("Heap[");
	String comma = "";
	for (int i = 0; i < numElems; i++) {
	    sb.append(comma).append(elems[i]);
	    comma=",";
	}
	return sb.append("]").toString();
    }
}
