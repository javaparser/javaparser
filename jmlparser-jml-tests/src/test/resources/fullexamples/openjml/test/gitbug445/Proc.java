public interface Proc<T,S> {
    //@ assignable objectState;
    S run(T x);
}
