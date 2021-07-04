import java.util.LinkedList;
import java.util.List;

// This used to compare a \TYPE to null - which is no longer allowed - but still need to sort out whether \elemtype can return null
public class Bug1 {

    public static void main(String... args) {
        LinkedList<?>[] a = new LinkedList<?>[1];
        a[0] = new LinkedList<Boolean>();
        int k = 0; Object o = new Object();
        //@ ghost \TYPE t = \elemtype(\typeof(a));
        //@ assert (\lbl TY t) == \type(LinkedList);
        //@ assert (\lbl TY2 \typeof(k)) == \type(int);
        //@ set  t = (\lbl TY3 \elemtype(\typeof(k)));
        //@ set  t = (\lbl TY4 \elemtype(\typeof(o)));

        System.out.println("END");
    }
}
