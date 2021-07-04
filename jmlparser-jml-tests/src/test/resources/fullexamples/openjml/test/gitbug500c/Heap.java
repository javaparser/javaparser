
public class Heap implements PriorityQueue {
    private Comparable[] elems;
    private int numElems;

    /*@ private represents size <- numElems; @*/

    public Heap() {
	elems = new Comparable[5];
	numElems = 0;
    }

    /*@ ensures elems.length > \old(elems.length)
      @       && numElems == \old(numElems);
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
	int parent = pos / 2;
	while (pos > 0 && elems[parent].compareTo(o) > 0) {
	    elems[pos] = elems[parent];
	    pos = parent;
	    parent = pos / 2;
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
}
