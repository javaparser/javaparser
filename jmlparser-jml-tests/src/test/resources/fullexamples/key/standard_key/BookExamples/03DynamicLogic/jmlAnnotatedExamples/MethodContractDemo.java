public class MethodContractDemo {

    int attr;

  /*@ public normal_behavior
    @ assignable \nothing;
    @ ensures \result == x+1;
    @*/
  public int inc(int x) {      
      return ++x;
  }


    
  /*@ public normal_behavior
    @    ensures \result == u+1 && attr == 100;
    @ */
  public int init(int u) {
      attr = 100;
      return inc(u);
  }

}
