public class Sum {
  //@ requires 0 <= x < Integer.MAX_VALUE/2;
  //@ ensures \result == 2*x;
  public static int sum(int x){
    int r;
    if (x==0) r = 0;
    else {
      r = sum(x-1);
      //@ assert r == 2*(x-1);
      r = r + 2;
    } 
    return r;    
  }
}