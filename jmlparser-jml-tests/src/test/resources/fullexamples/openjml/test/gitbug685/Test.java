import java.util.Arrays;
public class Test {
    //@ requires \forall int i; 0 <= i && i < a.length; \typeof(a[i]) <: \type(Comparable<Object>);
    void f(Object[] a) {
       Arrays.sort(a);
       //@ assert a != null; // works
       Arrays.sort(a, (Object o1, Object o2) -> 0);
       //@ assert a != null; // <-- Test.java: warning: There is no feasible path to program point at program exit in method Test.f(java.lang.Object[])
    }
}