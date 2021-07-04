// This test is just here to see if unimplemented cquantifier constructs are handled without giving outright errors,
// though they won't prove.
public class Test {
  //@ ensures \result == (\sum int i; 0 <= i && i < a.length; a[i]);
  public int foo(int[] a) {
     int sum = 0;
     //@ loop_invariant 0 <= \count && \count <= a.length;
     //@ loop_invariant sum == (\sum int j; 0<=j && j<\count; a[j]);
     for (int k: a) {
        sum = sum + k;
     }
     return sum;
  }
}