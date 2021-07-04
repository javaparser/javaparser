// Fails with rac - gitbug536 - this fails to compile (AssertionError) when run outside of Eclipse
public class Test536 {

    //@requires \forall int i; 0 <= i && i < array.length-1; array[i] <= array[i+1];
    public static void doesNothingButRequiresSorted(int[] array) {
    }

    //@requires \forall int i; (\bigint)0 <= i && i < array.length-1; array[i] <= array[i+1];
    public static void doesNothingButRequiresSortedC(int[] array) {
    }

    //@requires \forall Integer i; 0 <= i && i < array.length-1; array[i] <= array[i+1];
    public static void doesNothingButRequiresSortedInteger(Integer[] array) {
    }

    //@requires \forall Integer i; 0 <= i && i < array.length-1; array[i] <= array[i+1];
    public static void doesNothingButRequiresSortedInteger(int[] array) {
    }

  public static void main(String[] args) {
      int[] array0 = {0,1,2,3};
      int[] array1 = {0,1,2,-3};
      Integer[] array2 = {0,1,2,3};
      Integer[] array3 = {0,1,2,-3};

      // Succeeds
      doesNothingButRequiresSorted(array0);
      // Fails
      doesNothingButRequiresSorted(array1);
      // Succeeds
      doesNothingButRequiresSortedC(array0);
      // Fails
      doesNothingButRequiresSortedC(array1);
      // Succeeds
      doesNothingButRequiresSortedInteger(array2);
      // Fails
      doesNothingButRequiresSortedInteger(array3);
      // Succeeds
      doesNothingButRequiresSortedInteger(array0);
      // Fails
      doesNothingButRequiresSortedInteger(array1);
  }
}
