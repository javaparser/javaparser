public interface AProc<T> {
    /*@ public normal_behavior
      @   requires 0 <= i < a.length;
      @   requires \nonnullelements(a);
      @   assignable objectState, a[i];   @*/
    void run(T[] a, int i);
}
