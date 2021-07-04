import java.io.*;

public class Test2 {
    public static class Foo implements Comparable {
	int value;
	public Foo(int i) {
	    value = i;
	}
	public int compareTo(Object o) {
	    System.err.println("compare "+this+" and "+o);
	    return value - ((Foo)o).value;
	}

	public String toString() {
	    return String.valueOf(value);
	}
    }
	    
	    

    public static void main(String[] param) throws IOException {
	PriorityQueue pq = new Heap();
	int j = 1;
	for (int i = 0; i < 200; i++) {
	    pq.enqueue(new Integer(j));
	    j = (107*j +13) % 999983;
	}
	while (!pq.isEmpty()) {
	    System.err.println(""+pq.removeFirst());
	}
    }
}
