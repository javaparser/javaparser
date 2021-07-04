import java.util.Queue;
public class Test {
    void f1(Queue<Integer> q) {
        //@ loop_modifies q.values;
        //@ loop_invariant \invariant_for(q);
        while (!q.isEmpty())
            q.poll();
    }
}