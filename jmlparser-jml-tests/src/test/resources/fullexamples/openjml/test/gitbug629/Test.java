class Node {
    int data;
    /*@ nullable */ Node next;
}
public class Test {
    public Node getLast(Node head) {
        if (head == null)
            return null;

        Node node = head;
        // @ ???
        while (node.next != null) {
            node = node.next;
            if (node.equals(head)) {
                throw new RuntimeException();
            }
        }
        return node;
    }
}