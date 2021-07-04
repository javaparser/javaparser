import java.io.*;

public class Test {
    public static void main(String[] param) throws IOException {
	BufferedReader reader = 
	    new BufferedReader(new InputStreamReader(System.in));
	PriorityQueue pq = new Heap();
	while (true) {
	    System.out.print("<number> or r: ");
	    String input = reader.readLine();
	    switch (input.charAt(0)) {
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
		    try {
			int value = Integer.parseInt(input);
			pq.enqueue(new Integer(value));
		    } catch (NumberFormatException ex) {
			System.out.println("Invalid Number: "+ex);
		    }
			break;
		case 'r':
		    if (!pq.isEmpty()) {
			Integer out = (Integer) pq.removeFirst();
			System.out.println("First is "+out);
		    } else {
			System.out.println("Queue is empty!");
		    }
		    break;
		case 'x':
		    return;
	    }
	}
    }
}
