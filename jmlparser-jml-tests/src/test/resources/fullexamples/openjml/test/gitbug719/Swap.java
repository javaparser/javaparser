public class Swap {
/*@ requires 0 <= i && i < arr.length 
             && 0 <= j && j < arr.length;
  @ requires \nonnullelements(arr);  
  @ assignable arr[i], arr[j];
  @ ensures \old(arr[i]) == arr[j] 
	     && \old(arr[j]) == arr[i];
  @ ensures arr.length == \old(arr.length);
  @ ensures \nonnullelements(arr);  
  @*/
  public <T> void swap(int i, int j, T arr[]) {
	  T temp;     
      temp = arr[i];
      arr[i] = arr[j];
      arr[j] = temp;
  }
}
