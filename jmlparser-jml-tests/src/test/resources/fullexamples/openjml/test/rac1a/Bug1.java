import java.util.LinkedList;
import java.util.List;

// Simplified version of test rac1
// Still need to sort out whether \elemtype can return null
public class Bug1 {

    public static void main(String... args) {
        LinkedList<?>[] a = new LinkedList<?>[1];
        a[0] = new LinkedList<Boolean>();
        System.out.println("END");
    }
}
