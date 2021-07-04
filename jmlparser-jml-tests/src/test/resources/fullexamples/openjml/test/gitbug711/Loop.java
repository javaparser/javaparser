public class Loop {
  //@ requires i >= 0;
  public static void m(int i) {
    zasd:
        //@ loop_invariant i >= 0;
        //@ loop_writes i;
    for (;i>0;) {
      i -= 1;
      if (i != 0) continue zasd;
    }
  }
}
