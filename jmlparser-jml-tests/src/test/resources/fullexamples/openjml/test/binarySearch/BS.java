public class BS {
  
  //@ requires values != null;
  //@ requires (\forall int i, j; 0 <= i && i < j && j < values.length; values[i] <= values[j]);
  //@ ensures -1 < \result && \result < values.length;
  int binarySearch(int[] values, int x) {
  //@ assert values != null && (\forall int i; 0 < i < values.length; values[i-1] <= values[i]);
  //@ assume !(\forall int i; 0 <= i < values.length; values[i] != x);
  //@ reachable;
        try {
                int y =  java.util.Arrays.binarySearch(values, x);
                return y;
        }
        catch(Exception e) {
                return -1;
        }
  }

}