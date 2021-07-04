public class ArrOps<T> {
    /* @ extract @*/  // FIXME - what does extract do?
    //@ requires \nonnullelements(a);
    public void forEach(T[] a, AProc<T> p) {
        //@ loop_invariant 0 <= i <= a.length;
        //@ decreasing a.length - i;
        for (int i = 0; i < a.length; i++) {
            p.run(a, i);
        }
    }
}
